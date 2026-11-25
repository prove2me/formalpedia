-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_hasFDerivAt_fsPotPlane_87791490bbb3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:03:41.47303+00:00
-- url     : https://prove2.me/submissions/53cbc30f-fde0-45c6-8780-d6bab6986647

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFsPotLaplacian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PFsPotLaplacian

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
theorem _root_.solution (z : ℂ) :
    HasFDerivAt fsPotPlane ((1 + ‖z‖ ^ 2)⁻¹ • innerSL ℝ z) z := by
  have hl : HasFDerivAt (fun y : ℂ => Real.log (1 + ‖y‖ ^ 2))
      ((1 + ‖z‖ ^ 2)⁻¹ • (2 • innerSL ℝ z)) z :=
    ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add 1).log (by positivity)
  have e : fsPotPlane = fun y : ℂ => Real.log (1 + ‖y‖ ^ 2) * (1 / 2) := by
    funext y; simp only [fsPotPlane]; ring
  rw [e]
  refine (hl.mul_const (1 / 2 : ℝ)).congr_fderiv ?_
  ext w
  simp
  ring
end GroundTheory.Heights₂.Heights.LowerBoundFree
