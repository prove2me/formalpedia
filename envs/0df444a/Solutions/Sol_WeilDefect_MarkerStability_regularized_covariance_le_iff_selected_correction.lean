-- Prove2me | solution 1 for WeilDefect.MarkerStability.regularized_covariance_le_iff_selected_correction
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T22:23:17.75923+00:00
-- url     : https://prove2.me/submissions/fae1b104-63ab-47ce-9e73-c186b5f0d790

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder
noncomputable section
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Positive regularization supplies a true inverse even for dependent columns. -/
theorem covariance_regularization_strictPositive (P : K →L[ℂ] H) (δ : ℝ) (hδ : 0 < δ) :
    IsStrictlyPositive (P ∘L P.adjoint + δ • 1) :=
  IsStrictlyPositive.nonneg_add
    ((ContinuousLinearMap.nonneg_iff_isPositive (f := P ∘L P.adjoint)).mpr
      (isPositive_self_comp_adjoint P)) (isStrictlyPositive_one.smul hδ)

/-- Rectangular Woodbury identity on the ORIGINAL Hilbert spaces. The coefficient
inverse is regularized; no column Gram invertibility or independence is assumed. -/
theorem regularized_covariance_inverse_woodbury (P : K →L[ℂ] H)
    (δ : ℝ) (hδ : 0 < δ) :
    Ring.inverse (P ∘L P.adjoint + δ • 1) =
      δ⁻¹ • (1 - P ∘L Ring.inverse (P.adjoint ∘L P + δ • 1) ∘L P.adjoint) := by
  let A : H →L[ℂ] H := P ∘L P.adjoint + δ • 1
  let B : K →L[ℂ] K := P.adjoint ∘L P + δ • 1
  have hA : IsStrictlyPositive A := covariance_regularization_strictPositive P δ hδ
  have hB : IsStrictlyPositive B := by
    simpa only [adjoint_adjoint] using covariance_regularization_strictPositive P.adjoint δ hδ
  have hpush (a : K) : A (P a) = P (B a) := by
    simp only [A, B, add_apply, comp_apply, smul_apply, one_apply_eq_self, map_add,
      RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
  have hcancel (a : K) : B (Ring.inverse B a) = a := by
    change (B * Ring.inverse B) a = a
    rw [Ring.mul_inverse_cancel B hB.isUnit]
    rfl
  have hprod : A * (1 - P ∘L Ring.inverse B ∘L P.adjoint) = δ • 1 := by
    ext x
    change A (x - P (Ring.inverse B (P.adjoint x))) = δ • x
    rw [map_sub, hpush, hcancel]
    simp only [A, add_apply, comp_apply, smul_apply, one_apply_eq_self]
    abel
  have hright : A * (δ⁻¹ • (1 - P ∘L Ring.inverse B ∘L P.adjoint)) = 1 := by
    rw [mul_smul_comm, hprod, smul_smul, inv_mul_cancel₀ hδ.ne', one_smul]
  change Ring.inverse A = δ⁻¹ • (1 - P ∘L Ring.inverse B ∘L P.adjoint)
  calc
    Ring.inverse A = Ring.inverse A * 1 := (mul_one _).symm
    _ = Ring.inverse A * (A * (δ⁻¹ • (1 - P ∘L Ring.inverse B ∘L P.adjoint))) := by rw [hright]
    _ = (Ring.inverse A * A) * (δ⁻¹ • (1 - P ∘L Ring.inverse B ∘L P.adjoint)) := (mul_assoc _ _ _).symm
    _ = δ⁻¹ • (1 - P ∘L Ring.inverse B ∘L P.adjoint) := by
      rw [Ring.inverse_mul_cancel A hA.isUnit, one_mul]

private theorem inverse_nonnegative_helper (A : H →L[ℂ] H) (hA : IsStrictlyPositive A) :
    0 ≤ (Ring.inverse A) := by
  rw [Ring.inverse_of_isUnit hA.isUnit]
  exact CFC.inv_nonneg_of_nonneg hA.isUnit.unit (by simpa using hA.nonneg)


private theorem cost_nonnegative_helper (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) : 0 ≤ (N.adjoint ∘L Ring.inverse A ∘L N) := by
  have hp := ((ContinuousLinearMap.nonneg_iff_isPositive (f := Ring.inverse A)).mp (inverse_nonnegative_helper A hA)).conj_adjoint N.adjoint
  apply (ContinuousLinearMap.nonneg_iff_isPositive (f := N.adjoint ∘L Ring.inverse A ∘L N)).mpr
  simpa only [adjoint_adjoint] using hp


private theorem cost_le_one_of_covariance_le_helper (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) (hcov : N ∘L N.adjoint ≤ A) : (N.adjoint ∘L Ring.inverse A ∘L N) ≤ 1 := by
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive (f := A - N ∘L N.adjoint)).mp (sub_nonneg.mpr hcov)
  have hc := (ContinuousLinearMap.nonneg_iff_isPositive (f := N.adjoint ∘L Ring.inverse A ∘L N)).mp (cost_nonnegative_helper A hA N)
  apply sub_nonneg.mp
  apply (ContinuousLinearMap.nonneg_iff_isPositive (f := 1 - N.adjoint ∘L Ring.inverse A ∘L N)).mpr
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨(ContinuousLinearMap.isPositive_one : (1 : K →L[ℂ] K).IsPositive).isSelfAdjoint.sub hc.isSelfAdjoint, ?_⟩
  intro v
  let y := (Ring.inverse A) (N v)
  have hAy : A y = N v := by
    change (A ∘L (Ring.inverse A)) (N v) = _
    exact congrArg (fun T : H →L[ℂ] H => T (N v)) (Ring.mul_inverse_cancel A hA.isUnit)
  have hy : RCLike.re ⟪A y, y⟫_ℂ = RCLike.re ⟪v, (N.adjoint ∘L Ring.inverse A ∘L N) v⟫_ℂ := by
    rw [hAy, ← N.adjoint_inner_right]
    rfl
  have hb := hp.re_inner_nonneg_left y
  have he := N.adjoint.apply_norm_sq_eq_inner_adjoint_left y
  simp only [ContinuousLinearMap.adjoint_adjoint] at he
  simp only [sub_apply, inner_sub_left, map_sub] at hb
  rw [hy, ← he] at hb
  change 0 ≤ RCLike.re ⟪v, (N.adjoint ∘L Ring.inverse A ∘L N) v⟫_ℂ - ‖(N.adjoint ∘L Ring.inverse A ∘L N) v‖ ^ 2 at hb
  have hs := sq_nonneg ‖v - (N.adjoint ∘L Ring.inverse A ∘L N) v‖
  rw [@norm_sub_sq ℂ] at hs
  change 0 ≤ RCLike.re ⟪(1 - (N.adjoint ∘L Ring.inverse A ∘L N)) v, v⟫_ℂ
  simp only [sub_apply, one_apply_eq_self, inner_sub_left, map_sub, inner_self_eq_norm_sq]
  rw [inner_re_symm ((N.adjoint ∘L Ring.inverse A ∘L N) v) v]
  linarith


private theorem covariance_le_of_cost_le_one_helper (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) (hcost : (N.adjoint ∘L Ring.inverse A ∘L N) ≤ 1) : N ∘L N.adjoint ≤ A := by
  have hAp := (ContinuousLinearMap.nonneg_iff_isPositive (f := A)).mp hA.nonneg
  have hcp := (ContinuousLinearMap.nonneg_iff_isPositive (f := 1 - N.adjoint ∘L Ring.inverse A ∘L N)).mp (sub_nonneg.mpr hcost)
  apply sub_nonneg.mp
  apply (ContinuousLinearMap.nonneg_iff_isPositive (f := A - N ∘L N.adjoint)).mpr
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨hAp.isSelfAdjoint.sub (ContinuousLinearMap.isPositive_self_comp_adjoint N).isSelfAdjoint, ?_⟩
  intro x
  let a := N.adjoint x
  let y := (Ring.inverse A) (N a)
  have hAy : A y = N a := by
    change (A ∘L (Ring.inverse A)) (N a) = _
    have h := Ring.mul_inverse_cancel A hA.isUnit
    exact congrArg (fun T : H →L[ℂ] H => T (N a)) h
  have ha : RCLike.re ⟪N a, x⟫_ℂ = ‖a‖ ^ 2 := by
    rw [← N.adjoint_inner_right]
    exact inner_self_eq_norm_sq a
  have hy : RCLike.re ⟪N a, y⟫_ℂ = RCLike.re ⟪(N.adjoint ∘L Ring.inverse A ∘L N) a, a⟫_ℂ := by
    rw [← N.adjoint_inner_right]
    change RCLike.re ⟪a, (N.adjoint ∘L Ring.inverse A ∘L N) a⟫_ℂ = _
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

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- Exact clearing of the positive regularization in the selected inverse cost. -/
theorem regularized_selected_correction_eq_scaled_cost (P : K →L[ℂ] H)
    (N : L →L[ℂ] H) (δ : ℝ) (hδ : 0 < δ) :
    δ • (1 : L →L[ℂ] L) - N.adjoint ∘L N +
      (P.adjoint ∘L N).adjoint ∘L Ring.inverse (P.adjoint ∘L P + δ • 1) ∘L
        (P.adjoint ∘L N) =
    δ • (1 - N.adjoint ∘L Ring.inverse (P ∘L P.adjoint + δ • 1) ∘L N) := by
  rw [regularized_covariance_inverse_woodbury P δ hδ]
  simp only [adjoint_comp, adjoint_adjoint, comp_smul, smul_comp,
    comp_sub, sub_comp, one_def, comp_id, id_comp, smul_sub, smul_smul,
    mul_inv_cancel₀ hδ.ne', one_smul, comp_assoc]
  abel

/-- A physical covariance comparison is exactly a correction on the selected
coefficient space. The only inverse acts on the POSITIVE coefficient space and
is strictly positive by δ > 0, without an independent-column assumption. -/
theorem solution (P : K →L[ℂ] H)
    (N : L →L[ℂ] H) (δ : ℝ) (hδ : 0 < δ) :
    N ∘L N.adjoint ≤ P ∘L P.adjoint + δ • 1 ↔
    0 ≤ δ • (1 : L →L[ℂ] L) - N.adjoint ∘L N +
      (P.adjoint ∘L N).adjoint ∘L Ring.inverse (P.adjoint ∘L P + δ • 1) ∘L
        (P.adjoint ∘L N) := by
  have hA := covariance_regularization_strictPositive P δ hδ
  have hi : N ∘L N.adjoint ≤ P ∘L P.adjoint + δ • 1 ↔
      N.adjoint ∘L Ring.inverse (P ∘L P.adjoint + δ • 1) ∘L N ≤ 1 :=
    ⟨cost_le_one_of_covariance_le_helper _ hA N,
      covariance_le_of_cost_le_one_helper _ hA N⟩
  rw [regularized_selected_correction_eq_scaled_cost P N δ hδ]
  constructor
  · intro h
    exact smul_nonneg hδ.le (sub_nonneg.mpr (hi.mp h))
  · intro h
    apply hi.mpr
    apply sub_nonneg.mp
    have hs := smul_nonneg (inv_pos.mpr hδ).le h
    simpa only [smul_smul, inv_mul_cancel₀ hδ.ne', one_smul] using hs
