-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_sumW_line1_79c607502991
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:38.939459+00:00
-- url     : https://prove2.me/submissions/2ad29189-2b88-4141-8251-1526c1fb9fc9

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
theorem _root_.solution (f : ExW .line1 → ℝ) : ∑ i, f i = f (Sum.inl ()) + f (Sum.inr ()) := by
  have h : ∀ g : Unit ⊕ Unit → ℝ, ∑ i, g i = g (Sum.inl ()) + g (Sum.inr ()) := fun g => by
    simp [Fintype.sum_sum_type]
  exact h f
end GroundTheory.Heights₂.Heights.Inter
