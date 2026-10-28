-- Prove2me | solution 1 for SelfScaledIPM.ShortStep.eq_6_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T02:53:57.675451+00:00
-- url     : https://prove2.me/submissions/e5b10009-9c0f-404b-9200-7f05e29485b6

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_ConvexOptimization_IsBacktrackingStep
import Definitions.Def_ConvexOptimization_selfConcordance
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace

namespace Aux_SSIPM610
open SelfScaledIPM.ShortStep

lemma hess_inner {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (w u v : EuclideanSpace ℝ (Fin n)) :
    ⟪hess F w u, v⟫_ℝ = fderiv ℝ (fderiv ℝ F) w u v := by
  have hg : gradient F = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm ∘
      fderiv ℝ F := by
    funext x; rfl
  unfold hess
  rw [hg, LinearIsometryEquiv.comp_fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  exact InnerProductSpace.toDual_symm_apply

lemma hess_symm {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n))
    (hF : ContDiffAt ℝ 3 F w) (u v : EuclideanSpace ℝ (Fin n)) :
    ⟪hess F w u, v⟫_ℝ = ⟪hess F w v, u⟫_ℝ := by
  rw [hess_inner, hess_inner]
  have := hF.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)
  exact this u v

lemma euler {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hd : DifferentiableAt ℝ F x) (hhom : ∀ τ : ℝ, 0 < τ → F (τ • x) = F x - ν * Real.log τ) :
    ⟪gradient F x, x⟫_ℝ = -ν := by
  have h1 : HasDerivAt (fun τ : ℝ => F (τ • x)) (fderiv ℝ F x x) 1 := by
    have h3 : HasDerivAt (fun τ : ℝ => τ • x) x 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
    have hd1 : HasFDerivAt F (fderiv ℝ F x) ((1 : ℝ) • x) := by
      rw [one_smul]; exact hd.hasFDerivAt
    exact hd1.comp_hasDerivAt (1 : ℝ) h3
  have h2 : HasDerivAt (fun τ : ℝ => F (τ • x)) (-ν) 1 := by
    have h4 : HasDerivAt (fun τ : ℝ => F x - ν * Real.log τ) (-ν) 1 := by
      have := ((Real.hasDerivAt_log one_ne_zero).const_mul ν).const_sub (F x)
      simpa using this
    apply h4.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with τ hτ
    exact hhom τ hτ
  have := h1.unique h2
  rw [gradient, InnerProductSpace.toDual_symm_apply]
  exact this

end Aux_SSIPM610

open SelfScaledIPM.ShortStep Aux_SSIPM610 in
theorem solution {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hA : Function.Surjective A)
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (s : EuclideanSpace ℝ (Fin n))
    (hP : IsPrimalStrict K A b x) (hD : IsDualStrict K A c y s)
    (w : EuclideanSpace ℝ (Fin n)) (hw : IsScalingPoint K F x s w) (μp : ℝ)
    (qx : EuclideanSpace ℝ (Fin n)) (qy : EuclideanSpace ℝ (Fin m)) (qs : EuclideanSpace ℝ (Fin n))
    (hq : IsShortStepDir F A x s w μp qx qy qs) :
    A (x - qx) = b ∧ ContinuousLinearMap.adjoint A (y - qy) + (s - qs) = c ∧
      mu ν (x - qx) (s - qs) = μp := by
  obtain ⟨hq1, hq2, hq3⟩ := hq
  refine ⟨?_, ?_, ?_⟩
  · rw [map_sub, hP.2, hq2, sub_zero]
  · rw [map_sub, ← hD.2]
    have : ContinuousLinearMap.adjoint A qy = -qs := eq_neg_of_add_eq_zero_left hq3
    rw [this]; abel
  · have hcd : ContDiffOn ℝ 3 F (interior K) := hF.1.1.2.1
    have hopen : IsOpen (interior K) := isOpen_interior
    have hFw : ContDiffAt ℝ 3 F w := hcd.contDiffAt (hopen.mem_nhds hw.1)
    have hFx : ContDiffAt ℝ 3 F x := hcd.contDiffAt (hopen.mem_nhds hP.1)
    have hdx : DifferentiableAt ℝ F x := hFx.differentiableAt (by norm_num)
    have he := euler F ν x hdx (hF.1.2.2.2.1 x hP.1)
    -- ⟪qs, qx⟫ = 0
    have hqsqx : ⟪qs, qx⟫_ℝ = 0 := by
      have : qs = -ContinuousLinearMap.adjoint A qy := by
        rw [eq_neg_of_add_eq_zero_left hq3, neg_neg]
      rw [this, inner_neg_left, ContinuousLinearMap.adjoint_inner_left, hq2, inner_zero_right,
        neg_zero]
    -- ⟪s, qx⟫ = ⟪hess qx, x⟫
    have hsqx : ⟪s, qx⟫_ℝ = ⟪hess F w qx, x⟫_ℝ := by
      rw [← hw.2]; exact hess_symm F w hFw x qx
    -- ⟪qs, x⟫ from the Newton equation
    have hqsx : ⟪qs, x⟫_ℝ = ⟪s, x⟫_ℝ + μp * ⟪gradient F x, x⟫_ℝ - ⟪hess F w qx, x⟫_ℝ := by
      have : qs = s + μp • gradient F x - hess F w qx := by rw [← hq1]; abel
      rw [this, inner_sub_left, inner_add_left, inner_smul_left]
      simp
    have hν0 : ν ≠ 0 := by linarith
    unfold mu
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hqsqx, hsqx, hqsx, he]
    field_simp
    ring
