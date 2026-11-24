-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_redTwo_surjective_df3f27242c65
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:36.848309+00:00
-- url     : https://prove2.me/submissions/64889548-81e3-4cac-be9a-c50a304d6fa6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution : Function.Surjective redTwo :=
  MvPolynomial.map_surjective _ (ZMod.intCast_surjective)
end GroundTheory.Heights₂.Heights.Inter
