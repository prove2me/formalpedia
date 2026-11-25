-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_aeval_eq_eval__e50f1199a6e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:16:28.985569+00:00
-- url     : https://prove2.me/submissions/544f6a2c-d3d2-4045-8b57-be30f43f9762

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointNagata

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointNagata
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointNagata
theorem _root_.solution {S : Type*} [CommRing S] [Algebra ℤ S] (v : (Σ k, ι k) → S) (f : MRing ι) :
    aeval v f = eval₂ (Int.castRingHom S) v f := by
  rw [aeval_def, show algebraMap ℤ S = Int.castRingHom S from RingHom.ext_int _ _]
end GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointNagata
