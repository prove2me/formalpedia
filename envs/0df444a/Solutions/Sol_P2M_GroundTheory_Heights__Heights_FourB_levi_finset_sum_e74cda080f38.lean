-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_levi_finset_sum_e74cda080f38
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:13.444133+00:00
-- url     : https://prove2.me/submissions/368c85c1-8099-42a5-a5d1-c72de6b9e04d

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
variable {ι : Type*} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution {κ : Type*} (s : Finset κ) (F : κ → (ι → ℂ) → ℝ)
    (hF : ∀ j ∈ s, ContDiffAt ℝ 2 (F j) 0) (w : ι → ℂ) :
    levi (fun z => ∑ j ∈ s, F j z) 0 w = ∑ j ∈ s, levi (F j) 0 w := by
  have hev : ∀ᶠ z in 𝓝 (0 : ι → ℂ), ∀ j ∈ s, DifferentiableAt ℝ (F j) z := by
    rw [Filter.eventually_all_finset]
    intro j hj
    exact ((hF j hj).eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have h1 : fderiv ℝ (fun z => ∑ j ∈ s, F j z) =ᶠ[𝓝 0] fun z => ∑ j ∈ s, fderiv ℝ (F j) z := by
    filter_upwards [hev] with z hz
    simpa only [Finset.sum_fn] using fderiv_sum hz
  have h2 : fderiv ℝ (fderiv ℝ fun z => ∑ j ∈ s, F j z) 0 =
      ∑ j ∈ s, fderiv ℝ (fderiv ℝ (F j)) 0 := by
    rw [h1.fderiv_eq]
    simpa only [Finset.sum_fn] using fderiv_sum fun j hj =>
      ((hF j hj).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  simp only [levi, h2, _root_.sum_apply]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
end GroundTheory.Heights₂.Heights.FourB
