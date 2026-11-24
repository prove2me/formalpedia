-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_tensor_sqMetric_a_2f747b7be4bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:39.146889+00:00
-- url     : https://prove2.me/submissions/c15d5342-b00b-4917-938c-f7c0b56b43de

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDerived
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ConservationDegreeFormOfExistence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PConsequences

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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {A : HermLine ι} {α β : K → ℕ} (h : ∀ k, (α k : ℤ) - β k = A.a k) (k : K) :
    (A.tensor (HermLine.sqMetric β)).a k = α k := by
  show A.a k + (β k : ℤ) = α k
  rw [← h k]
  ring
end GroundTheory.Heights₂.Heights.Inter
