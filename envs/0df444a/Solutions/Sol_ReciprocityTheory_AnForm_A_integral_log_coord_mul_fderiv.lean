-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.integral_log_coord_mul_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:32:56.397728+00:00
-- url     : https://prove2.me/submissions/f6050c6e-e007-49e8-9ddf-2fe1514211b8

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrable_log_coord_mul
import Theorems.Thm_ReciprocityTheory_AnForm_A_logCoordLocInt_thm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Laplacian Pointwise
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} (j : Fin (D + 1)) {g : (Fin (D + 1) → ℂ) → ℝ}
    (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g) {x : Fin (D + 1) → ℂ} (hx : x j = 0) :
    ∫ z, Real.log ‖z j‖ * fderiv ℝ g z x = 0 := by
  set f : (Fin (D + 1) → ℂ) → ℝ := fun z => Real.log ‖z j‖ with hf
  have hfl : LocallyIntegrable f volume := logCoordLocInt_thm (D + 1) j
  have hfm : AEStronglyMeasurable f volume := hfl.aestronglyMeasurable
  have hgc : Continuous g := hg.continuous
  have hg' : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hfs : HasCompactSupport (fderiv ℝ g) := hs.fderiv ℝ
  obtain ⟨C, hC⟩ := (hg'.clm_apply continuous_const : Continuous fun z => fderiv ℝ g z x
    ).bounded_above_of_compact_support (hs.fderiv_apply ℝ x)
  set K : Set (Fin (D + 1) → ℂ) := tsupport (fderiv ℝ g) + Metric.closedBall (0 : Fin (D + 1) → ℂ) ‖x‖ with hKdef
  have hK : IsCompact K := hfs.isCompact.add (isCompact_closedBall _ _)
  set F : ℝ → (Fin (D + 1) → ℂ) → ℝ := fun t z => f z * g (z + t • x) with hF
  set F' : ℝ → (Fin (D + 1) → ℂ) → ℝ := fun t z => f z * fderiv ℝ g (z + t • x) x with hF'
  have hconst : ∀ t, ∫ z, F t z = ∫ z, f z * g z := by
    intro t
    have h : ∀ z, F t z = (fun z => f z * g z) (z + t • x) := by
      intro z; simp [hF, hf, hx]
    simp_rw [h]
    exact integral_add_right_eq_self (fun z => f z * g z) (t • x)
  have hmeas : ∀ᶠ t in nhds (0 : ℝ), AEStronglyMeasurable (F t) volume :=
    Filter.Eventually.of_forall fun t =>
      hfm.mul (hgc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
  have hint : Integrable (F 0) volume := by
    simpa [hF] using integrable_log_coord_mul j hgc hs
  have hmeas' : AEStronglyMeasurable (F' 0) volume :=
    hfm.mul (((hg'.comp (continuous_id.add continuous_const)).clm_apply
      continuous_const).aestronglyMeasurable)
  have hbound : ∀ᵐ z ∂(volume : Measure (Fin (D + 1) → ℂ)), ∀ t ∈ Metric.ball (0 : ℝ) 1,
      ‖F' t z‖ ≤ K.indicator (fun z => C * ‖f z‖) z := by
    refine Filter.Eventually.of_forall fun z t ht => ?_
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz, hF', norm_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hz]
      have h0 : fderiv ℝ g (z + t • x) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        apply hz
        refine Set.mem_add.2 ⟨z + t • x, hmem, -(t • x), ?_, by simp⟩
        rw [Metric.mem_closedBall, dist_zero_right, norm_neg, norm_smul]
        have ht' : ‖t‖ < 1 := by simpa using ht
        nlinarith [norm_nonneg x, norm_nonneg t]
      simp [hF', h0]
  have hboundint : Integrable (K.indicator fun z => C * ‖f z‖) volume :=
    (integrable_indicator_iff hK.measurableSet).2 ((hfl.integrableOn_isCompact hK).norm.const_mul C)
  have hd : ∀ᵐ z ∂(volume : Measure (Fin (D + 1) → ℂ)), ∀ t ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (fun t => F t z) (F' t z) t := by
    refine Filter.Eventually.of_forall fun z t _ => ?_
    have h1 : HasDerivAt (fun t : ℝ => z + t • x) x t := by
      simpa using ((hasDerivAt_id t).smul_const x).const_add z
    have h2 := (hdiff (z + t • x)).hasFDerivAt.comp_hasDerivAt t h1
    exact h2.const_mul (f z)
  obtain ⟨-, hder⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) hmeas hint hmeas' hbound hboundint hd
  have hc : HasDerivAt (fun t => ∫ z, F t z) 0 0 := by
    simp_rw [hconst]; exact hasDerivAt_const _ _
  have := hder.unique hc
  simpa [hF'] using this
end ReciprocityTheory.AnForm.A
