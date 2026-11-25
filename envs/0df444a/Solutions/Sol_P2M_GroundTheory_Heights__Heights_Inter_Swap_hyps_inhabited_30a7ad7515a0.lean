-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_Swap_hyps_inhabited_30a7ad7515a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:34:07.604185+00:00
-- url     : https://prove2.me/submissions/d1cb10e6-f8f7-4559-87c7-8911704c333a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSectionOn_Xc_1d364d2feb4e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_divSupp_X_disjoint_74521f1af0e6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isArithVar_projLine_149b03129df9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_fsLine_27a26231cd0b


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
namespace Swap
theorem _root_.solution :
    IsArithVar (⊥ : Ideal (MRing (PBlk 2))) (0 + 2) ∧ IsSmoothHerm (fsLine 2) ∧
      IsSectionOn ⊥ (fsLine 2) (Xc 2 0) ∧ IsSectionOn ⊥ (fsLine 2) (Xc 2 1) ∧
      ∀ W, W ∈ divSupp (⊥ : Ideal (MRing (PBlk 2))) (Xc 2 0) → W ∉ divSupp ⊥ (Xc 2 1) :=
  ⟨isArithVar_projLine, isSmoothHerm_fsLine 2, isSectionOn_Xc 2 0, isSectionOn_Xc 2 1, divSupp_X_disjoint⟩
end Swap
end GroundTheory.Heights₂.Heights.Inter
