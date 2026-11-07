-- Prove2me | solution 1 for SchedComplexity.Tardiness.theorem_4d_knapsack_reducible
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T12:17:15.775784+00:00
-- url     : https://prove2.me/submissions/bf5e425b-3f47-4aa7-9db6-2233857fb058

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_Tardiness_Knapsack
import Definitions.Def_SchedComplexity_Tardiness_MultLang
import Definitions.Def_SchedComplexity_Tardiness_Construction
import Theorems.Thm_SchedComplexity_Tardiness_knapsack_wt_encoding_reduction
import Theorems.Thm_SchedComplexity_Tardiness_theorem_4d_equivalence

open SchedComplexity.Tardiness CookPvsNP ProjSchedTW.Complexity

theorem solution : PolyReducible SchedComplexity.OneMachine.knapsackLang wtLangMult := by
  rcases knapsack_wt_encoding_reduction with ⟨f, hf_poly, hf⟩
  refine ⟨f, hf_poly, fun x => ?_⟩
  rw [← hf x]
  constructor
  · rintro ⟨a_list, b, ha_list, hb, ⟨S, hS⟩, rfl⟩
    let t := a_list.length
    let a : Fin t → ℕ := fun j => a_list.get j
    have ha : ∀ j : Fin t, 0 < a j := fun j => ha_list (a_list.get j) (List.get_mem a_list j)
    have h_ofFn : List.ofFn a = a_list := List.ofFn_get a_list
    have h_ky : KnapsackYes a b := ⟨S, hS⟩
    have hb_le : b ≤ bigA a := by
      rw [← hS, bigA]
      exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    rcases lt_or_eq_of_le hb_le with hb_lt | hb_eq
    · refine Or.inl ⟨t, a, b, ha, hb, hb_lt, ?_, by rw [h_ofFn]⟩
      have hτ : 2 * tPrime a b + bigA a < 2 * tPrime a b + bigA a + 1 := Nat.lt_succ_self _
      exact (theorem_4d_equivalence a b (2 * tPrime a b + bigA a + 1) ha hb hb_lt hτ).mp h_ky
    · exact Or.inr ⟨t, a, b, ha, hb, hb_eq, by rw [h_ofFn]⟩
  · rintro (⟨t, a, b, ha, hb, hb_lt, hsched, rfl⟩ | ⟨t, a, b, ha, hb, hb_eq, rfl⟩)
    · have hτ : 2 * tPrime a b + bigA a < 2 * tPrime a b + bigA a + 1 := Nat.lt_succ_self _
      have h_ky : KnapsackYes a b :=
        (theorem_4d_equivalence a b (2 * tPrime a b + bigA a + 1) ha hb hb_lt hτ).mpr hsched
      rcases h_ky with ⟨S, hS⟩
      refine ⟨List.ofFn a, b, ?_, hb, ?_, rfl⟩
      · intro v hv
        rcases List.mem_ofFn.mp hv with ⟨j, rfl⟩
        exact ha j
      · refine ⟨S.map ⟨Fin.cast (List.length_ofFn).symm, Fin.cast_injective _⟩, ?_⟩
        rw [Finset.sum_map]
        simpa using hS
    · refine ⟨List.ofFn a, b, ?_, hb, ?_, rfl⟩
      · intro v hv
        rcases List.mem_ofFn.mp hv with ⟨j, rfl⟩
        exact ha j
      · refine ⟨Finset.univ, ?_⟩
        have hsum : (∑ j : Fin (List.ofFn a).length, (List.ofFn a).get j) = bigA a := by
          unfold bigA
          refine Fintype.sum_equiv (finCongr (List.length_ofFn)) _ _ (fun j => ?_)
          simp only [List.get_ofFn, finCongr_apply]
        rw [hsum, hb_eq]
