-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_R1_hyps_inhabited_bed2c6b07b11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:34:04.485436+00:00
-- url     : https://prove2.me/submissions/b78a80f9-42c2-4eea-9e00-3d1729c3714d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isArithVar_specZ_eeb304758483
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSectionOn_Xc_1d364d2feb4e
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
namespace R1
theorem _root_.solution :
    IsArithVar (⊥ : Ideal (MRing (PBlk 1))) 1 ∧ IsSmoothHerm (fsLine 1) ∧
      IsSectionOn ⊥ (fsLine 1) (Xc 1 0) :=
  ⟨isArithVar_specZ, isSmoothHerm_fsLine 1, isSectionOn_Xc 1 0⟩
end R1
end GroundTheory.Heights₂.Heights.Inter
