-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_contDiff_evalC_435b0b7923c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:21:55.737164+00:00
-- url     : https://prove2.me/submissions/e3619f69-141d-4171-95d6-a2b736af4245

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_IsMultiHomogPlaneCoordinate

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution (s : MRing ι) :
    ContDiff ℝ ∞ (fun z : (Σ k, ι k) → ℂ => eval z (map (Int.castRingHom ℂ) s)) := by
  induction s using MvPolynomial.induction_on with
  | C a => simpa only [map_C, eval_C] using contDiff_const
  | add p q hp hq => simpa only [map_add, eval_add] using hp.add hq
  | mul_X p i hp =>
    simpa only [map_mul, map_X, eval_mul, eval_X] using hp.mul (contDiff_apply ℝ ℂ i)
end GroundTheory.Heights₂.Heights.Targets
