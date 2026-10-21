-- Prove2me | solution 1 for SymPolyOpt.PowerSumLB.schur_hankel_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:02:44.2123+00:00
-- url     : https://prove2.me/submissions/3b07e3a0-16e5-43ed-8b1c-5d5931968588

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumLB_Setting

set_option autoImplicit false
open Matrix SymPolyOpt.PowerSumLB

theorem solution :
    ∀ (s : ℕ → ℝ) (r : ℕ), (hankel (r + 1) s).PosSemidef → (hankel r s).PosDef →
      (fun i : Fin r => s (r + i)) ⬝ᵥ ((hankel r s)⁻¹ *ᵥ fun i : Fin r => s (r + i))
        ≤ s (2 * r) := by
  intro s r hP hD
  set H : Matrix (Fin r) (Fin r) ℝ := hankel r s with hH
  set u : Fin r → ℝ := fun i => s (r + i) with hu
  set w : Fin r → ℝ := -(H⁻¹ *ᵥ u) with hw
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det _).mp hD.isUnit
  have hHw : H *ᵥ w = -u := by
    rw [hw, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have h1 : ∀ i : Fin r, ∑ j : Fin r, s ((i : ℕ) + (j : ℕ)) * w j = - u i := by
    intro i
    have := congrFun hHw i
    simpa [Matrix.mulVec, dotProduct, hH, hankel] using this
  have huw : u ⬝ᵥ w = -(u ⬝ᵥ (H⁻¹ *ᵥ u)) := by
    rw [hw, dotProduct_neg]
  set v : Fin (r + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) w 1 with hv
  have hq := hP.dotProduct_mulVec_nonneg v
  simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
    Fin.snoc_last, hankel, hv, Fin.val_castSucc, Fin.val_last] at hq
  have h2 : ∀ i : Fin r, s ((i : ℕ) + r) = u i := by
    intro i; simp [hu, add_comm]
  simp only [h1, h2, mul_one, one_mul] at hq
  have h3 : ∑ i : Fin r, w i * (-u i + u i) = 0 := by simp
  have h4 : ∑ j : Fin r, s (r + (j : ℕ)) * w j = u ⬝ᵥ w := by
    simp [dotProduct, hu]
  simp only [mul_add, Finset.sum_add_distrib] at hq
  have h5 : ∑ x : Fin r, w x * -u x = -∑ x : Fin r, w x * u x := by
    simp [Finset.sum_neg_distrib]
  rw [h5, h4, huw] at hq
  rw [two_mul]
  linarith
