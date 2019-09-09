{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC
    -ddump-splices
#-}

module Demo where

import StreamLib

fg :: IO Int
fg = $$ftest
