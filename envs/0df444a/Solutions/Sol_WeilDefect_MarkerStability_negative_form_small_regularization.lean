-- Prove2me | solution 1 for WeilDefect.MarkerStability.negative_form_small_regularization
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T06:38:54.017986+00:00
-- url     : https://prove2.me/submissions/a12d05a4-5b9c-40bb-94e1-c59bee33f568

import Definitions.Def_WeilMarker_regularized_cost
set_option autoImplicit false
open scoped InnerProduct ComplexOrder
open ContinuousLinearMap
noncomputable section
namespace WeilDefect.MarkerStability
open WeilDefect.WDT13
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
theorem inverse_nonnegative (A : H →L[ℂ] H) (hA : IsStrictlyPositive A) :
    0 ≤ operatorInverse A := by
  rw [operatorInverse, Ring.inverse_of_isUnit hA.isUnit]
  exact CFC.inv_nonneg_of_nonneg hA.isUnit.unit (by simpa using hA.nonneg)

theorem inverse_smul (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (c : ℝ) (hc : 0 < c) :
    operatorInverse (c • A) = c⁻¹ • operatorInverse A := by
  have hunit := (hA.smul hc).isUnit
  have hright : (c • A) * (c⁻¹ • operatorInverse A) = 1 := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_inv_cancel₀ hc.ne', one_smul]
    exact Ring.mul_inverse_cancel A hA.isUnit
  calc
    operatorInverse (c • A) = operatorInverse (c • A) * 1 := (mul_one _).symm
    _ = operatorInverse (c • A) * ((c • A) * (c⁻¹ • operatorInverse A)) := by rw [hright]
    _ = (operatorInverse (c • A) * (c • A)) * (c⁻¹ • operatorInverse A) := (mul_assoc _ _ _).symm
    _ = c⁻¹ • operatorInverse A := by
      rw [show operatorInverse (c • A) * (c • A) = 1 from Ring.inverse_mul_cancel _ hunit,
        one_mul]

theorem cost_nonnegative (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) : 0 ≤ selectedCost A N := by
  have hp := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (inverse_nonnegative A hA)).conj_adjoint N.adjoint
  simpa [selectedCost] using (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hp

theorem cost_mono {A B : H →L[ℂ] H}
    (hAB : A ≤ B) (hA : IsStrictlyPositive A) (N : K →L[ℂ] H) :
    selectedCost B N ≤ selectedCost A N := by
  have hi := CStarAlgebra.ringInverse_le_ringInverse hAB hA
  have hp := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (sub_nonneg.mpr hi)).conj_adjoint N.adjoint
  apply sub_nonneg.mp
  simpa [selectedCost, operatorInverse, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.sub_comp] using (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hp

theorem cost_smul (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) (c : ℝ) (hc : 0 < c) :
    selectedCost (c • A) N = c⁻¹ • selectedCost A N := by
  rw [selectedCost, inverse_smul A hA c hc]
  ext x
  simp [selectedCost]

theorem marker_nonnegative (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) : 0 ≤ marker A N :=
  inverse_nonnegative _ (isStrictlyPositive_one.add_nonneg (cost_nonnegative A hA N))

theorem marker_le_one (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) : marker A N ≤ 1 := by
  have h := CStarAlgebra.ringInverse_le_ringInverse
    (le_add_of_nonneg_right (cost_nonnegative A hA N)) isStrictlyPositive_one
  simpa [marker, operatorInverse] using h

/-- Relative covariance control gives marker control independent of inverse-cost size.
No bound on the selected synthesis or cost is a hypothesis. -/
theorem relative_marker_stability (A B : H →L[ℂ] H) (N : K →L[ℂ] H)
    (hA : IsStrictlyPositive A) (α : ℝ) (hα : 0 ≤ α) (hα1 : α < 1)
    (hlower : (1 - α) • A ≤ B) (hupper : B ≤ A) :
    IsStrictlyPositive B ∧ 0 ≤ marker A N - marker B N ∧
      ‖marker A N - marker B N‖ ≤ α := by
  have hc : 0 < 1 - α := sub_pos.mpr hα1
  have hB := (hA.smul hc).of_le hlower
  have hSA := cost_nonnegative A hA N
  have hSB := cost_nonnegative B hB N
  have hlo := cost_mono hupper hB N
  have hhi := cost_mono hlower (hA.smul hc) N
  rw [cost_smul A hA N (1 - α) hc] at hhi
  have hΓ : marker B N ≤ marker A N := by
    exact CStarAlgebra.ringInverse_le_ringInverse
      (add_le_add (le_refl 1) hlo) (isStrictlyPositive_one.add_nonneg hSA)
  have hscale : 1 + selectedCost B N ≤ (1 - α)⁻¹ • (1 + selectedCost A N) := by
    rw [smul_add]
    apply add_le_add _ hhi
    have : 1 ≤ (1 - α)⁻¹ := (one_le_inv₀ hc).mpr (by linarith)
    simpa only [one_smul] using
      smul_le_smul_of_nonneg_right this (zero_le_one : (0 : K →L[ℂ] K) ≤ 1)
  have hΓscale : (1 - α) • marker A N ≤ marker B N := by
    have hi := CStarAlgebra.ringInverse_le_ringInverse hscale
      (isStrictlyPositive_one.add_nonneg hSB)
    change operatorInverse ((1 - α)⁻¹ • (1 + selectedCost A N)) ≤ _ at hi
    rw [inverse_smul _ (isStrictlyPositive_one.add_nonneg hSA)
      ((1 - α)⁻¹) (inv_pos.mpr hc), inv_inv] at hi
    exact hi
  have hdiff : 0 ≤ marker A N - marker B N := sub_nonneg.mpr hΓ
  have hbound : marker A N - marker B N ≤ α • (1 : K →L[ℂ] K) := by
    calc
      marker A N - marker B N ≤ marker A N - (1 - α) • marker A N :=
        sub_le_sub_left hΓscale _
      _ = α • marker A N := by rw [sub_smul, one_smul]; abel
      _ ≤ α • (1 : K →L[ℂ] K) :=
        smul_le_smul_of_nonneg_left (marker_le_one A hA N) hα
  refine ⟨hB, hdiff, ?_⟩
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ hα hdiff).mpr
  simpa only [Algebra.algebraMap_eq_smul_one] using hbound

end WeilDefect.MarkerStability
open WeilDefect.MarkerStability


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace ComplexOrder
open ContinuousLinearMap
noncomputable section
namespace WeilDefect.MarkerStability
open WeilDefect.WDT13
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The exact half-threshold is the unit bound on the original selected inverse cost. -/
theorem half_bound_iff_cost_le_one (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) :
    (1 / 2 : ℝ) • (1 : K →L[ℂ] K) ≤ marker A N ↔ selectedCost A N ≤ 1 := by
  have hS := isStrictlyPositive_one.add_nonneg (cost_nonnegative A hA N)
  have htwo : IsStrictlyPositive ((2 : ℝ) • (1 : K →L[ℂ] K)) :=
    isStrictlyPositive_one.smul (by norm_num)
  have hhalf : IsStrictlyPositive ((1 / 2 : ℝ) • (1 : K →L[ℂ] K)) :=
    isStrictlyPositive_one.smul (by norm_num)
  have hΓ : IsStrictlyPositive (marker A N) := by
    unfold marker operatorInverse
    rw [Ring.inverse_of_isUnit hS.isUnit]
    exact ⟨CFC.inv_nonneg_of_nonneg hS.isUnit.unit (by simpa using hS.nonneg),
      Units.isUnit _⟩
  have hi2 : operatorInverse ((2 : ℝ) • (1 : K →L[ℂ] K)) = (1 / 2 : ℝ) • 1 := by
    rw [inverse_smul _ isStrictlyPositive_one _ (by norm_num)]
    simp [operatorInverse]
  have hih : operatorInverse ((1 / 2 : ℝ) • (1 : K →L[ℂ] K)) = (2 : ℝ) • 1 := by
    rw [inverse_smul _ isStrictlyPositive_one _ (by norm_num)]
    simp [operatorInverse]
  have hiΓ : operatorInverse (marker A N) = 1 + selectedCost A N := by
    exact Ring.inverse_inverse hS.isUnit
  constructor
  · intro h
    have hi := CStarAlgebra.ringInverse_le_ringInverse h hhalf
    change operatorInverse (marker A N) ≤ operatorInverse ((1 / 2 : ℝ) • 1) at hi
    rw [hiΓ, hih] at hi
    have ht : (2 : ℝ) • (1 : K →L[ℂ] K) = 1 + 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, add_smul, one_smul]
    rw [ht] at hi
    exact (add_le_add_iff_left 1).mp hi
  · intro h
    have hi := CStarAlgebra.ringInverse_le_ringInverse (show 1 + selectedCost A N ≤ 1 + 1 from add_le_add_right h 1) hS
    change operatorInverse (1 + 1 : K →L[ℂ] K) ≤ marker A N at hi
    have ht : (1 + 1 : K →L[ℂ] K) = (2 : ℝ) • 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, add_smul, one_smul]
    rwa [ht, hi2] at hi

/-- Completing the square in the original physical metric: a selected cost at
most one forces selected covariance domination, without a range assumption. -/
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

/-- The half-bound forces nonnegative original physical selected form. -/
theorem selected_form_nonnegative_of_half_bound (A : H →L[ℂ] H)
    (hA : IsStrictlyPositive A) (N : K →L[ℂ] H)
    (hhalf : (1 / 2 : ℝ) • (1 : K →L[ℂ] K) ≤ marker A N) (x : H) :
    ‖N.adjoint x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ := by
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (sub_nonneg.mpr (covariance_le_of_cost_le_one A hA N
      ((half_bound_iff_cost_le_one A hA N).mp hhalf)))
  have h := hp.re_inner_nonneg_left x
  simp only [ContinuousLinearMap.sub_apply, inner_sub_left, map_sub] at h
  have he := N.adjoint.apply_norm_sq_eq_inner_adjoint_left x
  simp only [ContinuousLinearMap.adjoint_adjoint] at he
  linarith

/-- A strict physical negative margin survives every sufficiently small Picard
regularization and forbids the marker half-bound. -/
theorem negative_form_forbids_half_bound (P : K →L[ℂ] H)
    {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    (N : J →L[ℂ] H) (x : H) (ε : ℝ) (hε : 0 < ε)
    (hgap : ε * ‖x‖ ^ 2 < ‖N.adjoint x‖ ^ 2 - ‖P.adjoint x‖ ^ 2) :
    ¬ (1 / 2 : ℝ) • (1 : J →L[ℂ] J) ≤ marker (P ∘L P.adjoint + ε • 1) N := by
  intro hhalf
  have hP : 0 ≤ P ∘L P.adjoint := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (ContinuousLinearMap.isPositive_self_comp_adjoint P)
  have hpos : IsStrictlyPositive (P ∘L P.adjoint + ε • 1) :=
    IsStrictlyPositive.nonneg_add hP (isStrictlyPositive_one.smul hε)
  have hb := selected_form_nonnegative_of_half_bound _ hpos N hhalf x
  have he := P.adjoint.apply_norm_sq_eq_inner_adjoint_left x
  simp only [ContinuousLinearMap.adjoint_adjoint] at he
  have hform : RCLike.re ⟪(P ∘L P.adjoint + ε • 1) x, x⟫_ℂ =
      ‖P.adjoint x‖ ^ 2 + ε * ‖x‖ ^ 2 := by
    letI := InnerProductSpace.rclikeToReal ℂ H
    simp only [add_apply, smul_apply, one_apply_eq_self, inner_add_left,
      inner_smul_real_left, map_add, map_smul, inner_self_eq_norm_sq, ← he]
    congr 1
    rw [← real_inner_eq_re_inner ℂ]
    exact (real_inner_smul_left x x ε).trans
      (congrArg (fun r : ℝ => ε * r) (real_inner_self_eq_norm_sq x))
  rw [hform] at hb
  linarith

/-- A negative original selected form gives a positive interval of failed
half-bounds; its width is the physical margin divided by `‖x‖²+1`. -/
theorem negative_form_small_regularization (P : K →L[ℂ] H)
    {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    (N : J →L[ℂ] H) (x : H)
    (hneg : ‖P.adjoint x‖ ^ 2 - ‖N.adjoint x‖ ^ 2 < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ¬ (1 / 2 : ℝ) • (1 : J →L[ℂ] J) ≤ marker (P ∘L P.adjoint + ε • 1) N := by
  let d := ‖N.adjoint x‖ ^ 2 - ‖P.adjoint x‖ ^ 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hn : 0 < ‖x‖ ^ 2 + 1 := by positivity
  refine ⟨d / (‖x‖ ^ 2 + 1), div_pos hd hn, ?_⟩
  intro ε hε he
  have hb := (lt_div_iff₀ hn).mp he
  apply negative_form_forbids_half_bound P N x ε hε
  dsimp [d] at hb
  nlinarith

end WeilDefect.MarkerStability

open WeilDefect.MarkerStability
theorem solution {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (P : K →L[ℂ] H) {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    (N : J →L[ℂ] H) (x : H)
    (hneg : ‖P.adjoint x‖ ^ 2 - ‖N.adjoint x‖ ^ 2 < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ¬ (1 / 2 : ℝ) • (1 : J →L[ℂ] J) ≤ marker (P ∘L P.adjoint + ε • 1) N :=
  negative_form_small_regularization P N x hneg
