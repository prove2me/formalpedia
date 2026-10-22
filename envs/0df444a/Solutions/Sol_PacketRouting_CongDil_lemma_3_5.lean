-- Prove2me | solution 1 for PacketRouting.CongDil.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:45:00.343063+00:00
-- url     : https://prove2.me/submissions/a300f84a-f164-4136-b460-f95cdd88109a

import Mathlib
import Definitions.Def_PacketRouting_CongDil_Timetable

set_option autoImplicit false
open PacketRouting.CongDil

lemma prc_frameCount_add {P E : Type*} [Fintype P] {path : P → List E} (τ : Timetable path)
    (g : E) (t a b : ℕ) :
    τ.frameCount g t (a + b) ≤ τ.frameCount g t a + τ.frameCount g (t + a) b := by
  classical
  unfold Timetable.frameCount
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hp ⊢
  obtain ⟨k, hk, h1, h2⟩ := hp
  by_cases hlt : τ.time p k < t + a
  · exact Or.inl ⟨k, hk, h1, hlt⟩
  · exact Or.inr ⟨k, hk, by omega, by omega⟩

theorem solution {P E : Type*} [Fintype P] {path : P → List E} (τ : Timetable path)
    (g : E) (R : ℝ) (T : ℕ) (hT : 1 ≤ T)
    (h : ∀ y t : ℕ, T ≤ y → y < 2 * T → (τ.frameCount g t y : ℝ) ≤ R * y) :
    ∀ y t : ℕ, T ≤ y → (τ.frameCount g t y : ℝ) ≤ R * y := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro t hy
    by_cases hy2 : y < 2 * T
    · exact h y t hy hy2
    · push_neg at hy2
      have h1 : (τ.frameCount g t T : ℝ) ≤ R * T := h T t le_rfl (by omega)
      have h2 : (τ.frameCount g (t + T) (y - T) : ℝ) ≤ R * ((y - T : ℕ) : ℝ) :=
        ih (y - T) (by omega) (t + T) (by omega)
      have h3 := prc_frameCount_add τ g t T (y - T)
      rw [show T + (y - T) = y by omega] at h3
      have h3' : (τ.frameCount g t y : ℝ) ≤ (τ.frameCount g t T : ℝ) + (τ.frameCount g (t + T) (y - T) : ℝ) := by
        exact_mod_cast h3
      have h4 : ((y - T : ℕ) : ℝ) = (y : ℝ) - T := by
        rw [Nat.cast_sub (by omega)]
      rw [h4] at h2
      nlinarith
