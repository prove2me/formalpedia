-- Prove2me | solution 1 for PosIndexNash.PPADS.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:15:56.645703+00:00
-- url     : https://prove2.me/submissions/fd5277f5-6c7f-4f25-9b34-b40af36c4229
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PosIndexNash_PPADS_PPADSClass
import Definitions.Def_PosIndexNash_PPADS_PositiveIndexNash
import Theorems.Thm_PosIndexNash_PPADS_theorem_3_2
import Theorems.Thm_PosIndexNash_PPADS_theorem_6_8
import Theorems.Thm_ConstrSOSP_searchReduces_trans

open PosIndexNash.PPADS

theorem solution : PPADSComplete PositiveIndexNash := by
  constructor
  · exact PosIndexNash.PPADS.theorem_3_2
  · intro R hR
    exact ConstrSOSP.searchReduces_trans R SinkOfLine PositiveIndexNash hR
      PosIndexNash.PPADS.theorem_6_8
