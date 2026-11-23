-- Prove2me | solution 1 for PosIndexNash.PPADS.theorem_6_8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:32:20.729854+00:00
-- url     : https://prove2.me/submissions/45058dc9-3c12-4534-af87-28c33b020bc8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ConstrSOSP_searchReduces_trans
import Theorems.Thm_PosIndexNash_PPADS_theorem_4_2_search_reduction
import Theorems.Thm_PosIndexNash_PPADS_section_5_search_reduction
import Theorems.Thm_PosIndexNash_PPADS_section_6_search_reduction

open PosIndexNash.PPADS

theorem solution : CardinalMatching.SearchReduces SinkOfLine PositiveIndexNash := by
  exact ConstrSOSP.searchReduces_trans SinkOfLine PositiveIndexFixedPoint PositiveIndexNash
    theorem_4_2_search_reduction
    (ConstrSOSP.searchReduces_trans PositiveIndexFixedPoint PositiveIndexLCP PositiveIndexNash
      section_5_search_reduction section_6_search_reduction)
