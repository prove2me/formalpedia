-- Prove2me | solution 1 for ProjSchedTW.Complexity.minDelayAlt_npComplete
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:49:16.178915+00:00
-- url     : https://prove2.me/submissions/29c162d8-5934-4361-a87b-7c15230ba494
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_ProjSchedTW_Complexity_DelayingAlternatives
import Theorems.Thm_CookPvsNP_npComplete_of_polyReducible
import Theorems.Thm_ProjSchedTW_Complexity_minDelayAltLang_mem_NP
import Theorems.Thm_ProjSchedTW_Complexity_subsetSum_polyReducible_minDelayAlt

set_option autoImplicit false

open CookPvsNP ProjSchedTW.Complexity

theorem solution (hSubsetSum : CookPvsNP.NPComplete subsetSumLang) :
    CookPvsNP.NPComplete minDelayAltLang :=
  npComplete_of_polyReducible subsetSumLang minDelayAltLang
    hSubsetSum minDelayAltLang_mem_NP subsetSum_polyReducible_minDelayAlt
