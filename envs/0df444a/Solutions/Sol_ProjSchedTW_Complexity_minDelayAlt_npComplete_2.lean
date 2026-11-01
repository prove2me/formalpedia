-- Prove2me | solution 2 for ProjSchedTW.Complexity.minDelayAlt_npComplete
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:13:56.943214+00:00
-- url     : https://prove2.me/submissions/dea0ddcf-f73e-45c9-aa67-e4fc92592de4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_ProjSchedTW_Complexity_DelayingAlternatives
import Theorems.Thm_CookPvsNP_npComplete_of_polyReducible
import Theorems.Thm_ProjSchedTW_Complexity_minDelayAltLang_mem_NP
import Theorems.Thm_ProjSchedTW_Complexity_subsetSum_polyReducible_minDelayAlt

open ProjSchedTW.Complexity CookPvsNP

theorem solution (hSubsetSum : CookPvsNP.NPComplete subsetSumLang) :
    CookPvsNP.NPComplete minDelayAltLang :=
  CookPvsNP.npComplete_of_polyReducible subsetSumLang minDelayAltLang hSubsetSum
    minDelayAltLang_mem_NP subsetSum_polyReducible_minDelayAlt
