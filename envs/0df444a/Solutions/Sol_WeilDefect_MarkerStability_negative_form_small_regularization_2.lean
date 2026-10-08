-- Prove2me | solution 2 for WeilDefect.MarkerStability.negative_form_small_regularization
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T17:10:08.921974+00:00
-- url     : https://prove2.me/submissions/2a03e268-ddcb-4e05-9968-afc3cfe1a7e6

import Theorems.Thm_WeilDefect_MarkerStability_half_bound_iff_covariance_le
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
theorem selected_form_nonnegative_of_half_bound (A : H →L[ℂ] H)
    (hA : IsStrictlyPositive A) (N : K →L[ℂ] H)
    (hhalf : (1 / 2 : ℝ) • (1 : K →L[ℂ] K) ≤ marker A N) (x : H) :
    ‖N.adjoint x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ := by
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (sub_nonneg.mpr ((WeilDefect.MarkerStability.half_bound_iff_covariance_le A hA N).mp hhalf))
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

end GreenQuadraticProof
open GreenQuadraticProof WeilDefect.MarkerStability
theorem solution {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (P : K →L[ℂ] H) {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    (N : J →L[ℂ] H) (x : H)
    (hneg : ‖P.adjoint x‖ ^ 2 - ‖N.adjoint x‖ ^ 2 < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ¬ (1 / 2 : ℝ) • (1 : J →L[ℂ] J) ≤ marker (P ∘L P.adjoint + ε • 1) N :=
  GreenQuadraticProof.negative_form_small_regularization P N x hneg
