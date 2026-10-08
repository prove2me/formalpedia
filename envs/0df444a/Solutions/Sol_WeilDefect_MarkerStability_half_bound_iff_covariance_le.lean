-- Prove2me | solution 1 for WeilDefect.MarkerStability.half_bound_iff_covariance_le
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T17:05:18.070787+00:00
-- url     : https://prove2.me/submissions/9818a89b-fdc5-42f3-ab34-362b4d6a78d6

import Theorems.Thm_WeilDefect_MarkerStability_marker_lower_iff_cost_upper
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace ComplexOrder
open ContinuousLinearMap
noncomputable section
namespace GreenQuadraticProof
open WeilDefect.WDT13 WeilDefect.MarkerStability
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
theorem inverse_nonnegative (A : H →L[ℂ] H) (hA : IsStrictlyPositive A) :
    0 ≤ operatorInverse A := by
  rw [operatorInverse, Ring.inverse_of_isUnit hA.isUnit]
  exact CFC.inv_nonneg_of_nonneg hA.isUnit.unit (by simpa using hA.nonneg)
theorem cost_nonnegative (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) : 0 ≤ selectedCost A N := by
  have hp := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (inverse_nonnegative A hA)).conj_adjoint N.adjoint
  simpa [selectedCost] using (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hp
theorem covariance_le_of_cost_le_one (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) (hcost : selectedCost A N ≤ 1) : N ∘L N.adjoint ≤ A := by
  have hAp := (ContinuousLinearMap.nonneg_iff_isPositive _).mp hA.nonneg
  have hcp := (ContinuousLinearMap.nonneg_iff_isPositive _).mp (sub_nonneg.mpr hcost)
  apply sub_nonneg.mp
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨hAp.isSelfAdjoint.sub (ContinuousLinearMap.isPositive_self_comp_adjoint N).isSelfAdjoint, ?_⟩
  intro x
  let a := N.adjoint x
  let y := operatorInverse A (N a)
  have hAy : A y = N a := by
    change (A ∘L operatorInverse A) (N a) = _
    have h := Ring.mul_inverse_cancel A hA.isUnit
    exact congrArg (fun T : H →L[ℂ] H => T (N a)) h
  have ha : RCLike.re ⟪N a, x⟫_ℂ = ‖a‖ ^ 2 := by
    rw [← N.adjoint_inner_right]
    exact inner_self_eq_norm_sq a
  have hy : RCLike.re ⟪N a, y⟫_ℂ = RCLike.re ⟪selectedCost A N a, a⟫_ℂ := by
    rw [← N.adjoint_inner_right]
    change RCLike.re ⟪a, selectedCost A N a⟫_ℂ = _
    exact inner_re_symm _ _
  have hcross : RCLike.re ⟪A x, y⟫_ℂ = ‖a‖ ^ 2 := by
    rw [hAp.inner_left_eq_inner_right, hAy]
    exact (inner_re_symm _ _).trans ha
  have hc := hcp.re_inner_nonneg_left a
  have hp := hAp.re_inner_nonneg_left (x - y)
  simp only [map_sub, inner_sub_left, inner_sub_right, map_sub] at hp
  rw [hAy, ha, hy, hcross] at hp
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    inner_sub_left, map_sub, inner_self_eq_norm_sq] at hc
  change 0 ≤ RCLike.re ⟪(A - N ∘L N.adjoint) x, x⟫_ℂ
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    inner_sub_left, map_sub]
  change 0 ≤ RCLike.re ⟪A x, x⟫_ℂ - RCLike.re ⟪N a, x⟫_ℂ
  rw [ha]
  linarith
theorem cost_le_one_of_covariance_le (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) (hcov : N ∘L N.adjoint ≤ A) : selectedCost A N ≤ 1 := by
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive _).mp (sub_nonneg.mpr hcov)
  have hc := (ContinuousLinearMap.nonneg_iff_isPositive _).mp (cost_nonnegative A hA N)
  apply sub_nonneg.mp
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨(ContinuousLinearMap.isPositive_one : (1 : K →L[ℂ] K).IsPositive).isSelfAdjoint.sub hc.isSelfAdjoint, ?_⟩
  intro v
  let y := operatorInverse A (N v)
  have hAy : A y = N v := by
    change (A ∘L operatorInverse A) (N v) = _
    exact congrArg (fun T : H →L[ℂ] H => T (N v)) (Ring.mul_inverse_cancel A hA.isUnit)
  have hy : RCLike.re ⟪A y, y⟫_ℂ = RCLike.re ⟪v, selectedCost A N v⟫_ℂ := by
    rw [hAy, ← N.adjoint_inner_right]
    rfl
  have hb := hp.re_inner_nonneg_left y
  have he := N.adjoint.apply_norm_sq_eq_inner_adjoint_left y
  simp only [ContinuousLinearMap.adjoint_adjoint] at he
  simp only [sub_apply, inner_sub_left, map_sub] at hb
  rw [hy, ← he] at hb
  change 0 ≤ RCLike.re ⟪v, selectedCost A N v⟫_ℂ - ‖selectedCost A N v‖ ^ 2 at hb
  have hs := sq_nonneg ‖v - selectedCost A N v‖
  rw [@norm_sub_sq ℂ] at hs
  change 0 ≤ RCLike.re ⟪(1 - selectedCost A N) v, v⟫_ℂ
  simp only [sub_apply, one_apply_eq_self, inner_sub_left, map_sub, inner_self_eq_norm_sq]
  rw [inner_re_symm (selectedCost A N v) v]
  linarith

end GreenQuadraticProof
open WeilDefect.MarkerStability
theorem solution {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] H) (hA : IsStrictlyPositive A) (N : K →L[ℂ] H) :
    (1 / 2 : ℝ) • (1 : K →L[ℂ] K) ≤ marker A N ↔ N ∘L N.adjoint ≤ A  := by
  have hc : (1 / 2 : ℝ) • (1 : K →L[ℂ] K) ≤ marker A N ↔ selectedCost A N ≤ 1 := by
    convert marker_lower_iff_cost_upper A hA N (1 / 2) (by norm_num) using 1 <;> norm_num
  exact hc.trans ⟨GreenQuadraticProof.covariance_le_of_cost_le_one A hA N,
    GreenQuadraticProof.cost_le_one_of_covariance_le A hA N⟩
