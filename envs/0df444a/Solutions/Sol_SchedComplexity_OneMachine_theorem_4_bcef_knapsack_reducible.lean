-- Prove2me | solution 1 for SchedComplexity.OneMachine.theorem_4_bcef_knapsack_reducible
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T12:37:03.816792+00:00
-- url     : https://prove2.me/submissions/46303011-95dd-46ec-8284-3ea9b1fb12a7

import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_OneMachine_Problems
import Definitions.Def_SchedComplexity_OneMachine_Constructions
import Theorems.Thm_SchedComplexity_OneMachine_knapsack_bcef_encoding_reduction
import Theorems.Thm_SchedComplexity_OneMachine_theorem_4b_equivalence
import Theorems.Thm_SchedComplexity_OneMachine_theorem_4c_equivalence
import Theorems.Thm_SchedComplexity_OneMachine_theorem_4e_equivalence
import Theorems.Thm_SchedComplexity_OneMachine_theorem_4f_equivalence

open SchedComplexity.OneMachine CookPvsNP ProjSchedTW.Complexity

private lemma sum_univ_get (a : List ℕ) : (∑ j : Fin a.length, a.get j) = a.sum := by
  rw [← List.sum_ofFn, List.ofFn_get]

private lemma le_sum_of_knapsackYes {a : List ℕ} {b : ℕ} (h : KnapsackYes a b) : b ≤ a.sum := by
  rcases h with ⟨S, rfl⟩
  rw [← sum_univ_get a]
  exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)

private lemma knapsackYes_of_eq_sum {a : List ℕ} {b : ℕ} (h : b = a.sum) : KnapsackYes a b :=
  ⟨Finset.univ, by rw [sum_univ_get, h]⟩

private lemma reduce_of_equiv {L : Lang BSym} {P : List ℕ → ℕ → Prop}
    (hequiv : ∀ a b, (∀ v ∈ a, 0 < v) → 0 < b → b < a.sum → (KnapsackYes a b ↔ P a b))
    (hred : ∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      ∀ x : List BSym,
        ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧ P a b ∧ x = encNats (b :: a)) ∨
          (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
        f x ∈ L) :
    PolyReducible knapsackLang L := by
  rcases hred with ⟨f, hf_poly, hf⟩
  refine ⟨f, hf_poly, fun x => ?_⟩
  rw [← hf x]
  constructor
  · rintro ⟨a, b, ha, hb, hky, rfl⟩
    rcases lt_or_eq_of_le (le_sum_of_knapsackYes hky) with hb_lt | hb_eq
    · exact Or.inl ⟨a, b, ha, hb, hb_lt, (hequiv a b ha hb hb_lt).mp hky, rfl⟩
    · exact Or.inr ⟨a, b, ha, hb, hb_eq, rfl⟩
  · rintro (⟨a, b, ha, hb, hb_lt, hp, rfl⟩ | ⟨a, b, ha, hb, hb_eq, rfl⟩)
    · exact ⟨a, b, ha, hb, (hequiv a b ha hb hb_lt).mpr hp, rfl⟩
    · exact ⟨a, b, ha, hb, knapsackYes_of_eq_sum hb_eq, rfl⟩

theorem solution :
    PolyReducible knapsackLang langLmaxSumWC ∧
    PolyReducible knapsackLang langRnLmax ∧
    PolyReducible knapsackLang langSumWU ∧
    PolyReducible knapsackLang langRnUnitSumWU := by
  rcases knapsack_bcef_encoding_reduction with ⟨hB, hC, hE, hF⟩
  exact ⟨reduce_of_equiv theorem_4b_equivalence hB,
         reduce_of_equiv theorem_4c_equivalence hC,
         reduce_of_equiv theorem_4e_equivalence hE,
         reduce_of_equiv theorem_4f_equivalence hF⟩
