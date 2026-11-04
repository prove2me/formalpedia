-- Prove2me | solution 1 for RockafellianRelax.proposition_3_3_b
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-03T12:31:52.440215+00:00
-- url     : https://prove2.me/submissions/8e97d126-39aa-49c3-9c7b-e0d9991f3449

import Definitions.Def_RockafellianRelax_IsExact
import Definitions.Def_RockafellianRelax_argmin
import Definitions.Def_RockafellianRelax_tilt

open RockafellianRelax

private lemma argmin_le {α : Type*} (ψ : α → EReal) {x : α}
    (hx : x ∈ argmin ψ) (z : α) : ψ x ≤ ψ z := by
  have h : ψ x ≤ (⨅ y, ψ y) + (0 : EReal) := hx.2
  rw [add_zero] at h
  exact h.trans (iInf_le ψ z)

theorem solution {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (φ : (Fin n → ℝ) → EReal) (hf : IsRockafellian f φ) (ybar : Fin m → ℝ)
    (hne : (argmin φ).Nonempty)
    (h33 : ∀ xs : Fin n → ℝ, xs ∈ argmin φ →
      ((0 : Fin m → ℝ), xs) ∈ argmin (tilt f ybar)) :
    IsExact f φ ybar := by
  obtain ⟨xs, hxs⟩ := hne
  refine ⟨hf, ?_⟩
  intro u
  apply le_iInf
  intro x
  have hmin := argmin_le (tilt f ybar) (h33 xs hxs) (u, x)
  have hzero : tilt f ybar (0, xs) = f (0, xs) := by
    simp [tilt]
  rw [hzero] at hmin
  have hvalue : minValue f 0 ≤ f (0, xs) := iInf_le _ xs
  exact EReal.add_le_of_le_sub (hvalue.trans hmin)

#print axioms solution
