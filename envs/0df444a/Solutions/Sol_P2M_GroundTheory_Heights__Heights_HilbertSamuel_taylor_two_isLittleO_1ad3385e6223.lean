-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_taylor_two_isLittleO_1ad3385e6223
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:48.016906+00:00
-- url     : https://prove2.me/submissions/5dd0d17a-7e99-4051-9262-e64aadd2393d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComplexTaylor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PComplexTaylorTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Filter Topology Asymptotics ReciprocityTheory.AnForm Matrix Metric
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    (fun z => f (x + z) - f x - fderiv ℝ f x z - fderiv ℝ (fderiv ℝ f) x z z / 2)
      =o[𝓝 0] fun z => ‖z‖ ^ 2 := by
  set L := fderiv ℝ f x
  set H := fderiv ℝ (fderiv ℝ f) x with hHdef
  have hsymm : IsSymmSndFDerivAt ℝ f x := hf.isSymmSndFDerivAt (by simp)
  have hH : HasFDerivAt (fderiv ℝ f) H x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have ho := hasFDerivAt_iff_isLittleO_nhds_zero.1 hH
  have htend : Tendsto (fun z : E => x + z) (𝓝 0) (𝓝 x) := by
    have : Continuous fun z : E => x + z := continuous_const.add continuous_id
    simpa using this.tendsto (0 : E)
  have hdiff : ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℝ f (x + z) :=
    htend.eventually ((hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp))
  refine isLittleO_iff.2 fun ε hε => ?_
  have hb := (isLittleO_iff.1 ho hε).and hdiff
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hb
  filter_upwards [ball_mem_nhds (0 : E) hδ] with z hz
  set g : E → ℝ := fun w => f (x + w) - f x - L w - (2 : ℝ)⁻¹ • H w w with hg
  have hderiv : ∀ w ∈ ball (0 : E) δ, HasFDerivAt g (fderiv ℝ f (x + w) - L - H w) w := by
    intro w hw
    have h1 : HasFDerivAt (fun w => f (x + w)) ((fderiv ℝ f (x + w)).comp
        (ContinuousLinearMap.id ℝ E)) w :=
      (hball w hw).2.hasFDerivAt.comp w ((hasFDerivAt_id w).const_add x)
    have h2 : HasFDerivAt (fun w => H w w) ((H w).comp (ContinuousLinearMap.id ℝ E) + H.flip w) w :=
      H.hasFDerivAt.clm_apply (hasFDerivAt_id w)
    have h3 := ((h1.sub_const (f x)).sub L.hasFDerivAt).sub (h2.const_smul (2 : ℝ)⁻¹)
    refine h3.congr_fderiv ?_
    ext v
    simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, _root_.smul_apply, _root_.add_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    have := hsymm v w
    rw [← hHdef] at this
    rw [this]
    ring
  have hz' : ‖z‖ < δ := by simpa using hz
  have hsub : closedBall (0 : E) ‖z‖ ⊆ ball 0 δ := closedBall_subset_ball hz'
  have hbound : ∀ w ∈ closedBall (0 : E) ‖z‖, ‖fderiv ℝ f (x + w) - L - H w‖ ≤ ε * ‖z‖ := by
    intro w hw
    have hw' := (hball w (hsub hw)).1
    have hwz : ‖w‖ ≤ ‖z‖ := by simpa using hw
    calc ‖fderiv ℝ f (x + w) - L - H w‖ ≤ ε * ‖w‖ := hw'
      _ ≤ ε * ‖z‖ := by gcongr
  have hz0 : z ∈ closedBall (0 : E) ‖z‖ := by simp
  have hmvt := (convex_closedBall (0 : E) ‖z‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun w hw => (hderiv w (hsub hw)).hasFDerivWithinAt) hbound
    (mem_closedBall_self (norm_nonneg z)) hz0
  have hg0 : g 0 = 0 := by simp [hg]
  rw [hg0, sub_zero, sub_zero] at hmvt
  have : g z = f (x + z) - f x - L z - H z z / 2 := by
    simp only [hg, smul_eq_mul]; ring
  rw [← this, norm_pow, norm_norm]
  calc ‖g z‖ ≤ ε * ‖z‖ * ‖z‖ := hmvt
    _ = ε * ‖z‖ ^ 2 := by ring
end GroundTheory.Heights₂.Heights.HilbertSamuel
