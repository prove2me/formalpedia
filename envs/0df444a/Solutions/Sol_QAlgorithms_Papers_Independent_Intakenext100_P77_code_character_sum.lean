-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P77.code_character_sum
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T00:41:36.771196+00:00
-- url     : https://prove2.me/submissions/acffb7f4-7874-4cae-82a5-a68505c57527

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P77

open scoped BigOperators ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {n : ℕ}
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) (a : Fin n → ZMod 2)
    (ha : a ∉ binDual C) :
    (∑ c : C, if c.val ⬝ᵥ a = 0 then (1 : ℝ) else -1) = 0 := by
  have hx : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hne' : ¬ ∀ c ∈ C, c ⬝ᵥ a = 0 := ha
  push_neg at hne'
  obtain ⟨c0, hc0, hne⟩ := hne'
  have h1 : c0 ⬝ᵥ a = 1 := by
    rcases hx (c0 ⬝ᵥ a) with h | h
    · exact absurd h hne
    · exact h
  set f : C → ℝ := fun c => if c.val ⬝ᵥ a = 0 then (1 : ℝ) else -1 with hf
  have hS : ∑ c : C, f (c + ⟨c0, hc0⟩) = ∑ c : C, f c :=
    Equiv.sum_comp (Equiv.addRight (⟨c0, hc0⟩ : C)) f
  have hneg : ∀ c : C, f (c + ⟨c0, hc0⟩) = - f c := by
    intro c
    have hc : (c + ⟨c0, hc0⟩ : C).val ⬝ᵥ a = c.val ⬝ᵥ a + 1 := by
      rw [Submodule.coe_add, add_dotProduct, h1]
    simp only [hf]
    rw [hc]
    rcases hx (c.val ⬝ᵥ a) with h | h
    · rw [h, if_neg (show ¬ ((0 : ZMod 2) + 1 = 0) by decide), if_pos rfl]
    · rw [h, if_pos (show ((1 : ZMod 2) + 1 = 0) by decide),
        if_neg (show ¬ ((1 : ZMod 2) = 0) by decide)] <;> norm_num
  have hS2 : ∑ c : C, f c = -∑ c : C, f c := by
    rw [← Finset.sum_neg_distrib, ← hS]
    exact Finset.sum_congr rfl (fun c _ => hneg c)
  show ∑ c : C, f c = 0
  linarith
