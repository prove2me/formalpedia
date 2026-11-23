-- Prove2me | solution 1 for PosIndexNash.PPADS.theorem_3_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:50:08.110466+00:00
-- url     : https://prove2.me/submissions/9d717702-d9ee-460c-aa97-7c87263b5211
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_PosIndexNash_PPADS_PPADSClass
import Theorems.Thm_ConstrSOSP_searchReduces_trans
import Theorems.Thm_PosIndexNash_PPADS_positive_payoff_shift
import Theorems.Thm_PosIndexNash_PPADS_oriented_lemke_howson_reduction

open PosIndexNash.PPADS

theorem solution : PositiveIndexNash ∈ PPADSClass := by
  exact ConstrSOSP.searchReduces_trans PositiveIndexNash PositivePayoffNash SinkOfLine
    positive_payoff_shift oriented_lemke_howson_reduction
