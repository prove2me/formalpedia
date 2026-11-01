-- Prove2me | solution 2 for ProjSchedTW.Complexity.deviation_npHard
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:14:46.176673+00:00
-- url     : https://prove2.me/submissions/3061d3f7-48c7-4d88-a6aa-aed62b89398d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_ProjSchedTW_Complexity_TimeConstrained
import Theorems.Thm_CookPvsNP_polyReducible_trans
import Theorems.Thm_ProjSchedTW_Complexity_maxCut_polyReducible_deviation

open ProjSchedTW.Complexity CookPvsNP

theorem solution (hMaxCut : CookPvsNP.NPComplete maxCutLang) :
    ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : CookPvsNP.Lang Sym'),
      L' ∈ CookPvsNP.NP Sym' → CookPvsNP.PolyReducible L' deviationLang := by
  intro Sym' _ _ L' hL'
  exact CookPvsNP.polyReducible_trans (hMaxCut.2 Sym' L' hL') maxCut_polyReducible_deviation
