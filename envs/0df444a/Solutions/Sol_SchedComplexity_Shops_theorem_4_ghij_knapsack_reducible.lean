-- Prove2me | solution 1 for SchedComplexity.Shops.theorem_4_ghij_knapsack_reducible
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T12:37:04.461027+00:00
-- url     : https://prove2.me/submissions/dc987b53-5aa8-424d-bb23-224375500910

import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_Shops_Problems
import Definitions.Def_SchedComplexity_Shops_Constructions
import Theorems.Thm_SchedComplexity_Shops_knapsack_ghij_encoding_reduction
import Theorems.Thm_SchedComplexity_Shops_theorem_4g_equivalence
import Theorems.Thm_SchedComplexity_Shops_theorem_4h_equivalence
import Theorems.Thm_SchedComplexity_Shops_theorem_4i_equivalence
import Theorems.Thm_SchedComplexity_Shops_theorem_4j_equivalence

open SchedComplexity.Shops SchedComplexity.OneMachine CookPvsNP ProjSchedTW.Complexity

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
    PolyReducible SchedComplexity.OneMachine.knapsackLang langFlowRn ∧
    PolyReducible SchedComplexity.OneMachine.knapsackLang langFlowTree ∧
    PolyReducible SchedComplexity.OneMachine.knapsackLang langJob2Ops3 ∧
    PolyReducible SchedComplexity.OneMachine.knapsackLang langJob3Ops2 := by
  rcases knapsack_ghij_encoding_reduction with ⟨hG, hH, hI, hJ⟩
  exact ⟨reduce_of_equiv theorem_4g_equivalence hG,
         reduce_of_equiv theorem_4h_equivalence hH,
         reduce_of_equiv theorem_4i_equivalence hI,
         reduce_of_equiv theorem_4j_equivalence hJ⟩
