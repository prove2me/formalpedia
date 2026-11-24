-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagPull_prod_YBlk_228ddc3d6696
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:20.021332+00:00
-- url     : https://prove2.me/submissions/bc42e758-1529-4f01-b86b-91702d6cc346

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Inter.DiagPull
namespace GroundTheory.Heights₂.Heights.Inter.DiagPull
theorem _root_.solution {M : Type*} [CommMonoid M] (f : T.YBlk → M) : ∏ b, f b = f .base * (f .det * f .line) := by
  rw [show (Finset.univ : Finset T.YBlk) = {.base, .det, .line} from rfl]
  simp
end GroundTheory.Heights₂.Heights.Inter.DiagPull
