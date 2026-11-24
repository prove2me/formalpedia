-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_segreBlockEmbedding_injective_86ede2a182f9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:37.639976+00:00
-- url     : https://prove2.me/submissions/4fdf203b-ec30-4f80-9795-b79e51e0ee90

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
theorem _root_.solution (j : Fin 2) : Function.Injective (diagonalBlockIndex j) := by
  intro a b h
  fin_cases j <;> cases a <;> cases b <;> simp_all [diagonalBlockIndex]
end GroundTheory.Heights₂.Heights.Inter
