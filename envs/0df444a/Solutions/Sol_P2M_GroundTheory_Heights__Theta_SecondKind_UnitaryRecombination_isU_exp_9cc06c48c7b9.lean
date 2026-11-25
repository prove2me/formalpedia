-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_isU_exp_9cc06c48c7b9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:42:41.205271+00:00
-- url     : https://prove2.me/submissions/c57e504a-11ef-431a-bd1c-486bfe3b5634

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Theta.SecondKind
open GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
variable (F : OrthoFrame)
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution {p q : ℕ} {X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ}
    (hX : X ∈ indefiniteUnitaryLieAlgebra p q) : IsU (NormedSpace.exp X) := by
  have := (mem_indefiniteUnitaryGroup_iff p q).1
    ((isExpLieAlgebra_indefiniteUnitary p q).expUnit_mem X hX)
  simpa [IsU] using this
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
