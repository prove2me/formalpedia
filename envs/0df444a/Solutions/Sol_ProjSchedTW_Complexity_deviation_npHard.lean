-- Prove2me | solution 1 for ProjSchedTW.Complexity.deviation_npHard
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:49:16.800969+00:00
-- url     : https://prove2.me/submissions/e8d8d6e5-8beb-4ce0-b0ef-56266029ec93
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_ProjSchedTW_Complexity_TimeConstrained
import Theorems.Thm_CookPvsNP_polyReducible_trans
import Theorems.Thm_ProjSchedTW_Complexity_maxCut_polyReducible_deviation

set_option autoImplicit false

open CookPvsNP ProjSchedTW.Complexity

theorem solution (hMaxCut : CookPvsNP.NPComplete maxCutLang) :
    ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : CookPvsNP.Lang Sym'),
      L' ∈ CookPvsNP.NP Sym' → CookPvsNP.PolyReducible L' deviationLang := by
  intro Sym' _ _ L' hL'
  exact polyReducible_trans (hMaxCut.2 Sym' L' hL') maxCut_polyReducible_deviation
