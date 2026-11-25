-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.coeff2_det_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:21:57.060549+00:00
-- url     : https://prove2.me/submissions/3353c538-c125-48b4-a582-19a89afcbe14

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Theorems.Thm_ReciprocityTheory_AnForm_P_eq_map_C_add_X_sq_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Filter Topology Polynomial Matrix
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ[X])
    (d : n → ℂ) (hd : ∀ a, d a ≠ 0) (h0 : cf 0 P = diagonal d) (h1 : cf 1 P = 0) :
    P.det.coeff 2 = (∏ a, d a) * ∑ a, (d a)⁻¹ * cf 2 P a a := by
  set N : Matrix n n ℂ[X] := (P - (cf 0 P).map C).map (fun q => q.divX.divX) with hN
  set K : Matrix n n ℂ[X] := diagonal (fun a => C (d a)⁻¹) * N with hK
  have hP := eq_map_C_add_X_sq_smul P h1
  rw [← hN] at hP
  have hD : (cf 0 P).map C = diagonal (fun a => C (d a)) := by
    rw [h0, Matrix.diagonal_map (map_zero C)]

  have hfac : P = diagonal (fun a => C (d a)) * (1 + ((X : ℂ[X]) ^ 2) • K) := by
    have hone : diagonal (fun a => C (d a)) * diagonal (fun a => C (d a)⁻¹) = (1 : Matrix n n ℂ[X]) := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      rw [← map_mul, mul_inv_cancel₀ (hd a), map_one]
    rw [mul_add, mul_one, Matrix.mul_smul, hK, ← mul_assoc, hone, one_mul, ← hD]
    exact hP
  have hdet : P.det = C (∏ a, d a) * (1 + ((X : ℂ[X]) ^ 2) • K).det := by
    conv_lhs => rw [hfac]
    rw [Matrix.det_mul, Matrix.det_diagonal, map_prod]
  rw [hdet, Polynomial.coeff_C_mul, Matrix.det_one_add_smul]
  have e4 : ((X : ℂ[X]) ^ 2) ^ 2 = X ^ 4 := by ring
  rw [e4, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow', Polynomial.coeff_mul_X_pow']
  simp only [show ¬ (4 ≤ 2) by norm_num, show (2 ≤ 2) by norm_num, if_false, if_true, Nat.sub_self,
    add_zero, Polynomial.coeff_one, show (2 : ℕ) ≠ 0 by norm_num, if_false, zero_add]
  congr 1
  rw [Matrix.trace, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.diag_apply, hK, Matrix.diagonal_mul, Polynomial.coeff_C_mul, hN]
  simp [Polynomial.coeff_divX, cf]
end ReciprocityTheory.AnForm.P
