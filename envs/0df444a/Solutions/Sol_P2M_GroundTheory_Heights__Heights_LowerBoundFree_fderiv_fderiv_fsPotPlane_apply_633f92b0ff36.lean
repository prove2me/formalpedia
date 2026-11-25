-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_fderiv_fderiv_fsPotPlane_apply_633f92b0ff36
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:24:30.500959+00:00
-- url     : https://prove2.me/submissions/8cacebc6-023c-44c3-9bb6-c6d547dfc518

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFsPotLaplacian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PFsPotLaplacian
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_fderiv_fsPotPlane_apply_0c5a41bdcaea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_contDiff_fsPotPlane_33440de80d39


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open InnerProductSpace Laplacian Real MeasureTheory Filter Topology Set
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution (y e : ℂ) :
    fderiv ℝ (fderiv ℝ fsPotPlane) y e e =
      fderiv ℝ (fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹ * (z.re * e.re + z.im * e.im)) y e := by
  have hd : DifferentiableAt ℝ (fderiv ℝ fsPotPlane) y :=
    ((contDiff_fsPotPlane.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num)) y
  have h := fderiv_clm_apply hd (differentiableAt_const e)
  have hfun : (fun z : ℂ => fderiv ℝ fsPotPlane z e) =
      fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹ * (z.re * e.re + z.im * e.im) :=
    funext fun z => fderiv_fsPotPlane_apply z e
  rw [hfun] at h
  rw [h]
  simp
end GroundTheory.Heights₂.Heights.LowerBoundFree
