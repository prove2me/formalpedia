-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_add_right_cb154109d9da
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:23.116153+00:00
-- url     : https://prove2.me/submissions/1881e30d-a4cf-47e2-a256-0d61e3b443fc

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
variable (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
namespace GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
theorem _root_.solution (u v v' : Fin D → ℂ) : sesq H u (v + v') = sesq H u v + sesq H u v' := by
  simp only [sesq, smul_add, map_add]
  push_cast
  ring
end GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
