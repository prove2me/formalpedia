-- Prove2me | solution 1 for SchedComplexity.TotalCompletion.theorem_4a_knapsack_reducible
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T12:37:03.222008+00:00
-- url     : https://prove2.me/submissions/25c281d6-aafb-4568-a360-972d2cb9a318

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SchedComplexity_TotalCompletion_Knapsack
import Definitions.Def_SchedComplexity_TotalCompletion_SingleMachine
import Definitions.Def_SchedComplexity_TotalCompletion_Construction
import Theorems.Thm_SchedComplexity_TotalCompletion_knapsack_mult_encoding_reduction
import Theorems.Thm_SchedComplexity_TotalCompletion_theorem_4a_equivalence

open SchedComplexity.TotalCompletion

theorem solution : CookPvsNP.PolyReducible knapsackLang sumCLangMult := by
  rcases knapsack_mult_encoding_reduction with ⟨f, hf_poly, hf⟩
  refine ⟨f, hf_poly, fun x => ?_⟩
  rw [← hf x]
  constructor
  · rintro ⟨t, a, b, hinst, ⟨S, hS⟩, rfl⟩
    have hb_le : b ≤ sumA a := by
      rw [← hS, sumA]
      exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    rcases lt_or_eq_of_le hb_le with hb_lt | hb_eq
    · exact Or.inl ⟨t, a, b, hinst, hb_lt, (theorem_4a_equivalence a b hinst.1 hinst.2 hb_lt).mp ⟨S, hS⟩, rfl⟩
    · exact Or.inr ⟨t, a, b, hinst, hb_eq, rfl⟩
  · rintro (⟨t, a, b, hinst, hb_lt, hyes, rfl⟩ | ⟨t, a, b, hinst, hb_eq, rfl⟩)
    · exact ⟨t, a, b, hinst, (theorem_4a_equivalence a b hinst.1 hinst.2 hb_lt).mpr hyes, rfl⟩
    · exact ⟨t, a, b, hinst, ⟨Finset.univ, hb_eq.symm⟩, rfl⟩
