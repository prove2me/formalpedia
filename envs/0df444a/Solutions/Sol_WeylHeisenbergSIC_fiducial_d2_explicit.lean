-- Prove2me | solution 1 for WeylHeisenbergSIC.fiducial_d2_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-22T17:46:43.674883+00:00
-- url     : https://prove2.me/submissions/b878bb78-69c6-438e-838d-815391bd54a3

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem solution :
    ∃ ψ : ZMod 2 → ℂ,
      (∑ x : ZMod 2, Complex.normSq (ψ x)) = 1 ∧
      ∀ a b : ZMod 2, (a,b) ≠ (0,0) →
        Complex.normSq (∑ x : ZMod 2, star (ψ x) *
          (ZMod.stdAddChar (b*x) * ψ (x+a))) = (2+1 : ℝ)⁻¹ := by
  let r : ℝ := Real.sqrt 3
  let u : ℝ := Real.sqrt ((3 + r) / 6)
  let t : ℝ := Real.sqrt ((3 - r) / 12)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg 3
  have hr2 : r ^ 2 = 3 := by
    dsimp [r]
    norm_num
  have hr3 : r ≤ 3 := by nlinarith
  have hu0 : 0 ≤ (3 + r) / 6 := by positivity
  have ht0 : 0 ≤ (3 - r) / 12 := by positivity
  have hu2 : u ^ 2 = (3 + r) / 6 := by
    dsimp [u]
    simpa [pow_two] using Real.mul_self_sqrt hu0
  have ht2 : t ^ 2 = (3 - r) / 12 := by
    dsimp [t]
    simpa [pow_two] using Real.mul_self_sqrt ht0
  have hchar : ZMod.stdAddChar (1 : ZMod 2) = (-1 : ℂ) := by
    change ZMod.stdAddChar ((1 : ℤ) : ZMod 2) = (-1 : ℂ)
    rw [ZMod.stdAddChar_coe]
    rw [show (2 : ℂ) * Real.pi * Complex.I * (1 : ℤ) / (2 : ℕ) =
      (Real.pi : ℂ) * Complex.I by norm_num; ring]
    exact Complex.exp_pi_mul_I
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := rfl
  have hone : (1 : ZMod 2) ≠ 0 := by decide
  have hadd : (1 : ZMod 2) + 1 = 0 := by decide
  have zcases (x : ZMod 2) : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  let ψ : ZMod 2 → ℂ := fun x =>
    if x = 0 then (u : ℂ) else (t : ℂ) * (1 + Complex.I)
  refine ⟨ψ, ?_, ?_⟩
  · simp [ψ, huniv, Complex.normSq, hu2, ht2]
    nlinarith
  · intro a b hab
    rcases zcases a with rfl | rfl <;> rcases zcases b with rfl | rfl
    · exact (hab rfl).elim
    all_goals
      simp [ψ, huniv, hchar, hone, hadd, Complex.normSq]
      ring_nf
      nlinarith [hu2, ht2]
