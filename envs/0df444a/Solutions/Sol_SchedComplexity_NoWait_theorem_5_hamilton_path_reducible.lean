-- Prove2me | solution 1 for SchedComplexity.NoWait.theorem_5_hamilton_path_reducible
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T12:08:40.394985+00:00
-- url     : https://prove2.me/submissions/54ed3052-e103-48e9-b769-0af3a87c5356
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SchedComplexity_NoWait_DirectedGraphs
import Definitions.Def_SchedComplexity_NoWait_NoWaitFlowShop
import Definitions.Def_SchedComplexity_NoWait_Construction
import Theorems.Thm_SchedComplexity_NoWait_dhp_noWait_encoding_reduction
import Theorems.Thm_SchedComplexity_NoWait_theorem_5a_equiv
import Theorems.Thm_SchedComplexity_NoWait_theorem_5b_equiv
import Theorems.Thm_SchedComplexity_NoWait_iota_exists

open SchedComplexity.NoWait

theorem solution :
    CookPvsNP.PolyReducible dhpLang cmaxLang ∧
      CookPvsNP.PolyReducible dhpLang sumCLang := by
  rcases dhp_noWait_encoding_reduction with ⟨⟨fA, hfA_poly, hfA⟩, ⟨fB, hfB_poly, hfB⟩⟩
  refine ⟨⟨fA, hfA_poly, fun w => ?_⟩, ⟨fB, hfB_poly, fun w => ?_⟩⟩
  · rw [← hfA w]
    constructor
    · rintro ⟨n, adj, hhp, rfl⟩
      by_cases hn : n = 2
      · subst hn
        exact Or.inr ⟨adj, hhp, rfl⟩
      · refine Or.inl ⟨n, adj, hn, ?_, rfl⟩
        intro ι hι
        exact (theorem_5a_equiv adj ι hι 1 5 (by decide) (by decide)).mp hhp
    · rintro (⟨n, adj, hn, hsched, rfl⟩ | ⟨adj, hhp, rfl⟩)
      · rcases iota_exists n hn with ⟨ι, hι⟩
        exact ⟨n, adj, (theorem_5a_equiv adj ι hι 1 5 (by decide) (by decide)).mpr (hsched ι hι), rfl⟩
      · exact ⟨2, adj, hhp, rfl⟩
  · rw [← hfB w]
    constructor
    · rintro ⟨n, adj, hhp, rfl⟩
      by_cases hn : n = 2
      · subst hn
        exact Or.inr ⟨adj, hhp, rfl⟩
      · refine Or.inl ⟨n, adj, hn, ?_, rfl⟩
        intro ι hι
        exact (theorem_5b_equiv adj ι hι 1 5 (by decide) (by decide)).mp hhp
    · rintro (⟨n, adj, hn, hsched, rfl⟩ | ⟨adj, hhp, rfl⟩)
      · rcases iota_exists n hn with ⟨ι, hι⟩
        exact ⟨n, adj, (theorem_5b_equiv adj ι hι 1 5 (by decide) (by decide)).mpr (hsched ι hι), rfl⟩
      · exact ⟨2, adj, hhp, rfl⟩
