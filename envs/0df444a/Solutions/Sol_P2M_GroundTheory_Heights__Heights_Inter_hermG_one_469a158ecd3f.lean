-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_hermG_one_469a158ecd3f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:13.127719+00:00
-- url     : https://prove2.me/submissions/0cae4901-4eb1-4e23-b18d-009ecf2d9ea9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_TsgPolyVolPolyCoeffEven
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym

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
open MvPolynomial Matrix ComplexOrder ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
attribute [instance] ProjectiveLineBundle.fieldΩ ProjectiveLineBundle.finι ProjectiveLineBundle.finν ProjectiveLineBundle.finκ ProjectiveLineBundle.acgE ProjectiveLineBundle.modE
  ProjectiveLineBundle.fieldΦ ProjectiveLineBundle.algΦ
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (u w : Unit ⊕ Unit → ℂ) :
    hermG 1 u w = star (u (Sum.inl ())) * w (Sum.inl ()) + star (u (Sum.inr ())) * w (Sum.inr ()) := by
  simp [hermG, dotProduct, Fintype.sum_sum_type, Matrix.one_mulVec]
end GroundTheory.Heights₂.Heights.Inter
