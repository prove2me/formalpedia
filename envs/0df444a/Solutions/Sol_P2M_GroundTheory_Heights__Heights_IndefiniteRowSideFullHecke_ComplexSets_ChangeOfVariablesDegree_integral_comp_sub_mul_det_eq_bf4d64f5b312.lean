-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_integral_comp_sub_mul_det_eq_bf4d64f5b312
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:15:49.191233+00:00
-- url     : https://prove2.me/submissions/f78ad668-7a9b-4ed5-9053-e89efa6708f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChangeOfVariablesDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChangeOfVariablesDegreePiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChangeOfVariablesDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_continuous_det_fderiv_87e390290fc4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_hasCompactSupport_comp_sub_6ff964a89034
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_integral_fderiv_comp_mul_det_eq_zero_5ebf8e8b99be

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped ContDiff
open MeasureTheory Metric
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
theorem _root_.solution (φ : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hu : HasCompactSupport fun x => φ x - x)
    (f : (Fin (m + 1) → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (s : ℝ) :
    ∫ x, f (φ x - s • (Pi.single 0 1 : Fin (m + 1) → ℝ)) * (fderiv ℝ φ x).det =
      ∫ x, f (φ x) * (fderiv ℝ φ x).det := by
  set e : Fin (m + 1) → ℝ := Pi.single 0 1 with he
  obtain ⟨C, hC⟩ := (hφ.continuous.sub continuous_id).bounded_above_of_compact_support hu
  have hC' : ∀ x, ‖φ x - x‖ ≤ C := hC
  obtain ⟨r, hr⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨Cf, hCf⟩ := ((hf.continuous_fderiv (by simp)).clm_apply
    (continuous_const (y := e))).bounded_above_of_compact_support (hfc.fderiv_apply (𝕜 := ℝ) e)
  have hdc := continuous_det_fderiv φ hφ
  set Φ : ℝ → ℝ := fun s => ∫ x, f (φ x - s • e) * (fderiv ℝ φ x).det with hΦ
  have hderiv : ∀ s₀, HasDerivAt Φ 0 s₀ := by
    intro s₀
    set R := r + C + (|s₀| + 1) * ‖e‖ with hR
    set F' : ℝ → (Fin (m + 1) → ℝ) → ℝ :=
      fun s x => -(fderiv ℝ f (φ x - s • e) e) * (fderiv ℝ φ x).det with hF'
    have hbound : ∀ᵐ x ∂(volume : Measure (Fin (m + 1) → ℝ)), ∀ s ∈ ball s₀ 1,
        ‖F' s x‖ ≤ (closedBall (0 : Fin (m + 1) → ℝ) R).indicator
          (fun x => Cf * |(fderiv ℝ φ x).det|) x := by
      refine Filter.Eventually.of_forall fun x s hs => ?_
      by_cases hx : x ∈ closedBall (0 : Fin (m + 1) → ℝ) R
      · rw [Set.indicator_of_mem hx]
        simp only [hF', norm_mul, norm_neg, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hCf (φ x - s • e))
          (abs_nonneg _)
      · rw [Set.indicator_of_notMem hx]
        have hnot : φ x - s • e ∉ tsupport f := by
          intro hmem
          have h1 := hr hmem
          rw [mem_closedBall_zero_iff] at h1
          apply hx
          rw [mem_closedBall_zero_iff]
          have hs' : |s| ≤ |s₀| + 1 := by
            rw [mem_ball, Real.dist_eq] at hs
            have := abs_sub_abs_le_abs_sub s s₀
            linarith
          have hse : ‖s • e‖ ≤ (|s₀| + 1) * ‖e‖ := by
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right hs' (norm_nonneg _)
          have h2 : ‖x‖ ≤ ‖φ x - s • e‖ + ‖s • e‖ + ‖φ x - x‖ := by
            calc ‖x‖ = ‖(φ x - s • e) + s • e - (φ x - x)‖ := by congr 1; abel
              _ ≤ ‖(φ x - s • e) + s • e‖ + ‖φ x - x‖ := norm_sub_le _ _
              _ ≤ ‖φ x - s • e‖ + ‖s • e‖ + ‖φ x - x‖ := by gcongr; exact norm_add_le _ _
          linarith [hC' x]
        have h0 : fderiv ℝ f (φ x - s • e) = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hnot (tsupport_fderiv_subset ℝ h)
        simp [hF', h0]
    have hdiff : ∀ᵐ x ∂(volume : Measure (Fin (m + 1) → ℝ)), ∀ s ∈ ball s₀ 1,
        HasDerivAt (fun s => f (φ x - s • e) * (fderiv ℝ φ x).det) (F' s x) s := by
      refine Filter.Eventually.of_forall fun x s _ => ?_
      have hl : HasDerivAt (fun s : ℝ => φ x - s • e) (-e) s := by
        simpa using ((hasDerivAt_id s).smul_const e).const_sub (φ x)
      have := (((hf.differentiable (by simp)) (φ x - s • e)).hasFDerivAt.comp_hasDerivAt s
        hl).mul_const ((fderiv ℝ φ x).det)
      refine this.congr_deriv ?_
      simp only [hF', map_neg, neg_mul]
    have hcF : ∀ s : ℝ, Continuous fun x => f (φ x - s • e) * (fderiv ℝ φ x).det := fun s =>
      (hf.continuous.comp (hφ.continuous.sub continuous_const)).mul hdc
    have hcF' : Continuous (F' s₀) :=
      (((hf.continuous_fderiv (by simp)).comp (hφ.continuous.sub continuous_const)).clm_apply
        continuous_const).neg.mul hdc
    have hcB : Continuous fun x => Cf * |(fderiv ℝ φ x).det| := continuous_const.mul hdc.abs
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun s x => f (φ x - s • e) * (fderiv ℝ φ x).det) (F' := F') (x₀ := s₀)
      (bound := (closedBall (0 : Fin (m + 1) → ℝ) R).indicator
        fun x => Cf * |(fderiv ℝ φ x).det|)
      (ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall fun s => (hcF s).aestronglyMeasurable)
      ((hcF s₀).integrable_of_hasCompactSupport
        (hasCompactSupport_comp_sub φ C hC' f hfc _).mul_right)
      hcF'.aestronglyMeasurable
      hbound
      ((hcB.continuousOn.integrableOn_compact
        (isCompact_closedBall _ _)).integrable_indicator measurableSet_closedBall)
      hdiff
    have h0 : ∫ x, F' s₀ x = 0 := by
      simp only [hF', neg_mul, integral_neg]
      have hg := integral_fderiv_comp_mul_det_eq_zero φ hφ hu (fun y => f (y - s₀ • e))
        (hf.comp (contDiff_id.sub contDiff_const))
        (hfc.comp_homeomorph (Homeomorph.subRight (s₀ • e)))
      simp only [fderiv_comp_sub] at hg
      rw [hg, neg_zero]
    rw [← h0]
    exact key.2
  have hΦd : Differentiable ℝ Φ := fun s => (hderiv s).differentiableAt
  have := is_const_of_deriv_eq_zero hΦd (fun s => (hderiv s).deriv) s 0
  simpa [hΦ] using this
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
