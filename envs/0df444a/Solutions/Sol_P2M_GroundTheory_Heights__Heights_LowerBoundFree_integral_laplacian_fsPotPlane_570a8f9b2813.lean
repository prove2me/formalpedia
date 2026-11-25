-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_integral_laplacian_fsPotPlane_570a8f9b2813
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:10:46.734021+00:00
-- url     : https://prove2.me/submissions/ae146811-a30c-4343-85fc-6de0119437aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFsPotLaplacian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PFsPotLaplacian
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_laplacian_fsPotPlane_429c59d53f91
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_integral_radial_fsPot_93f9ec54b928

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
theorem _root_.solution : ∫ y, Δ fsPotPlane y = 2 * π := by
  have h : (fun y : ℂ => Δ fsPotPlane y) = fun y : ℂ => (fun s : ℝ => 2 / (1 + s ^ 2) ^ 2) ‖y‖ :=
    funext laplacian_fsPotPlane
  rw [h, integral_fun_norm_addHaar volume (fun s : ℝ => 2 / (1 + s ^ 2) ^ 2),
    Complex.finrank_real_complex, integral_radial_fsPot]
  simp [Measure.real, Complex.volume_ball]
end GroundTheory.Heights₂.Heights.LowerBoundFree
