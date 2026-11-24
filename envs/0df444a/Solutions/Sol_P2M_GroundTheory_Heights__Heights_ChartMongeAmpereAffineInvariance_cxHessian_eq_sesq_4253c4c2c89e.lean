-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_cxHessian_eq_sesq_4253c4c2c89e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:20.951022+00:00
-- url     : https://prove2.me/submissions/1a39a48a-4d06-4f66-ab6e-5d5b02773ade

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
theorem _root_.solution (f : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (i j : Fin D) :
    cxHessian f z i j = sesq (fderiv ℝ (fderiv ℝ f) z) (Pi.single i 1) (Pi.single j 1) := rfl
end GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
