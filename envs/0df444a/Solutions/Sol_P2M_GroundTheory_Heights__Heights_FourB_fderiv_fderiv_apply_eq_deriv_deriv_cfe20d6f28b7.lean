-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_fderiv_fderiv_apply_eq_deriv_deriv_cfe20d6f28b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:12.654461+00:00
-- url     : https://prove2.me/submissions/7401d2ab-3004-4654-bb22-84e568404484

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm Filter Topology Polynomial
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution {φ : E → ℝ} (hφ : ContDiffAt ℝ 2 φ 0) (v : E) :
    fderiv ℝ (fderiv ℝ φ) 0 v v = deriv (deriv fun t : ℝ => φ (t • v)) 0 := by
  have hev : ∀ᶠ y in 𝓝 (0 : E), DifferentiableAt ℝ φ y :=
    (hφ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hlin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t • v) v t := fun t => by
    simpa using (hasDerivAt_id t).smul_const v
  have hline : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 0) := by
    have : Continuous fun t : ℝ => t • v := continuous_id.smul continuous_const
    simpa using this.tendsto 0
  have hder : (deriv fun t : ℝ => φ (t • v)) =ᶠ[𝓝 0] fun t => fderiv ℝ φ (t • v) v := by
    filter_upwards [hline.eventually hev] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hlin t)).deriv
  rw [hder.deriv_eq]
  have h2 : DifferentiableAt ℝ (fderiv ℝ φ) 0 :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have h3 : HasDerivAt ((fderiv ℝ φ) ∘ fun t : ℝ => t • v) (fderiv ℝ (fderiv ℝ φ) 0 v) 0 :=
    h2.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hlin 0) (by simp)
  have h4 := h3.clm_apply (hasDerivAt_const (0 : ℝ) v)
  simpa using h4.deriv.symm
end GroundTheory.Heights₂.Heights.FourB
