-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_isSectionOn_Xc_1d364d2feb4e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:13.964636+00:00
-- url     : https://prove2.me/submissions/f153b3f6-4b14-430a-8f67-ec53e0acdea2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isMultiHomog_Xc_fc9bcb75d5ce

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
theorem _root_.solution (n : ℕ) (i : Fin n) : IsSectionOn ⊥ (fsLine n) (Xc n i) :=
  ⟨fun _ => 1, fun _ => rfl, isMultiHomog_Xc n i, by
    rw [Submodule.mem_bot]
    exact X_ne_zero _⟩
end GroundTheory.Heights₂.Heights.Inter
