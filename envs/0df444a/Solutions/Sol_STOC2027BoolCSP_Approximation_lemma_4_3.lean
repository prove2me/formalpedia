-- Prove2me | solution 1 for STOC2027BoolCSP.Approximation.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T05:23:34.113307+00:00
-- url     : https://prove2.me/submissions/fea10201-f878-48f0-b65c-0e3c339ef322

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Gaussian

open Matrix
open STOC2027BoolCSP.Approximation

theorem solution (m : ℕ) (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosDef) (η : ℝ) (hη : 0 < η)
    (hRJ : (R - η • onesMat m).PosSemidef) :
    (fun _ => (1 : ℝ)) ⬝ᵥ (R⁻¹ *ᵥ fun _ => (1 : ℝ)) ≤ η⁻¹  := by
  let v : Fin m → ℝ := R⁻¹ *ᵥ fun _ => 1
  let s : ℝ := ∑ i, v i
  have hv : R *ᵥ v = fun _ => 1 := by
    dsimp [v]
    rw [Matrix.mulVec_mulVec, R.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det _).mp hR.isUnit),
      Matrix.one_mulVec]
  have hJ : onesMat m *ᵥ v = fun _ => s := by
    ext i
    simp [Matrix.mulVec, dotProduct, onesMat, s]
  have h := hRJ.dotProduct_mulVec_nonneg v
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hv, hJ, dotProduct_sub,
    dotProduct_smul] at h
  have hq : s - η * (s*s) ≥ 0 := by
    simpa [dotProduct, Finset.sum_mul, s, smul_eq_mul] using h
  change ((fun _ => (1 : ℝ)) ⬝ᵥ v) ≤ η⁻¹
  change (∑ i, 1 * v i) ≤ η⁻¹
  simp only [one_mul]
  change s ≤ η⁻¹
  rw [← one_div, le_div_iff₀ hη]
  by_contra! hbig
  have hs : 0 < s := pos_of_mul_pos_left (lt_trans zero_lt_one hbig) hη.le
  nlinarith [mul_pos hs (sub_pos.mpr hbig)]

#print axioms solution
