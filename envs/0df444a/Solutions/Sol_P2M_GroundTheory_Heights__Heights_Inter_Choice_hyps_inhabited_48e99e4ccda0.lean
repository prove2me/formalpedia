-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_Choice_hyps_inhabited_48e99e4ccda0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:30.090862+00:00
-- url     : https://prove2.me/submissions/4ebf58ed-e192-495c-b603-bf4a63a3d785

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isClosedPt_two_76e35e7aefd3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isArithVar_projLine_149b03129df9


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
namespace Choice
theorem _root_.solution :
    IsArithVar (⊥ : Ideal (MRing (PBlk 2))) 2 ∧
      ∀ i : Fin 1, IsMultiProjPrime ((fun _ => ⊥ : Fin 1 → Ideal (MRing (PBlk 2))) i) ∧
        ⊥ ≤ (fun _ => ⊥ : Fin 1 → Ideal (MRing (PBlk 2))) i ∧
        (fun _ => ⊥ : Fin 1 → Ideal (MRing (PBlk 2))) i ≤ (fun _ => ptTwo) i ∧
        IsClosedPt ((fun _ => ptTwo : Fin 1 → Ideal (MRing (PBlk 2))) i) :=
  ⟨isArithVar_projLine, fun _ => ⟨isArithVar_projLine.2.1, le_rfl, bot_le, isClosedPt_two⟩⟩
end Choice
end GroundTheory.Heights₂.Heights.Inter
