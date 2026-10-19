-- Prove2me | solution 1 for SAG.SmallStep.complete_square
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T20:27:34.583808+00:00
-- url     : https://prove2.me/submissions/711e4415-10a7-4413-bd12-770e5689895c

import Mathlib
set_option autoImplicit false
open Matrix

theorem solution {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (hM : (-M).PosDef)
    (s t : Fin m → ℝ) :
    s ⬝ᵥ (M *ᵥ s) + s ⬝ᵥ t ≤ -(1 / 4) * (t ⬝ᵥ (M⁻¹ *ᵥ t)) := by
  have hsymm : Mᵀ = M := by
    have h := hM.isHermitian
    have h2 : (-M)ᴴ = -M := h
    rw [conjTranspose_neg, conjTranspose_eq_transpose_of_trivial] at h2
    exact neg_inj.mp h2
  have hdet : IsUnit M.det := by
    have h1 : IsUnit M := by simpa using hM.isUnit.neg
    exact (Matrix.isUnit_iff_isUnit_det M).mp h1
  set w : Fin m → ℝ := M⁻¹ *ᵥ t with hw
  have hMw : M *ᵥ w = t := by
    rw [hw, mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
  have hcomm : ∀ a b : Fin m → ℝ, a ⬝ᵥ (M *ᵥ b) = b ⬝ᵥ (M *ᵥ a) := by
    intro a b
    rw [dotProduct_mulVec, ← mulVec_transpose, hsymm, dotProduct_comm]
  have key : (s + (1/2 : ℝ) • w) ⬝ᵥ (M *ᵥ (s + (1/2 : ℝ) • w)) ≤ 0 := by
    by_cases h0 : s + (1/2 : ℝ) • w = 0
    · rw [h0]; simp
    · have := hM.dotProduct_mulVec_pos h0
      simp only [star_trivial, neg_mulVec, dotProduct_neg] at this
      linarith
  have e : (s + (1/2 : ℝ) • w) ⬝ᵥ (M *ᵥ (s + (1/2 : ℝ) • w))
      = s ⬝ᵥ (M *ᵥ s) + s ⬝ᵥ t + (1/4) * (t ⬝ᵥ w) := by
    rw [mulVec_add, mulVec_smul, hMw, add_dotProduct, dotProduct_add, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, hcomm w s, hMw, dotProduct_comm w t]
    ring
  linarith
