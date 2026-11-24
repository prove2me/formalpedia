-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_homogenise_dacb91173eef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:18.266745+00:00
-- url     : https://prove2.me/submissions/1543e648-c7ce-4482-b885-85de4ae352c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartNormPtsA

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.ChartNormPts
variable {P : Type*} {Q : Type*} [Fintype Q] {V : Type*}
namespace GroundTheory.Heights₂.Heights.Inter.ChartNormPts
theorem _root_.solution {R : Type*} [CommRing R] (v : P → V) (f g : Q → V)
    (F : MvPolynomial Q (MvPolynomial P ℤ)) (z : V → R) :
    aeval z (homogenise v f g F) =
      ∑ μ ∈ F.support, aeval (z ∘ v) (F.coeff μ) * ∏ q, z (f q) ^ μ q * z (g q) ^ (degreeOf q F - μ q) := by
  simp [homogenise, aeval_rename]
end GroundTheory.Heights₂.Heights.Inter.ChartNormPts
