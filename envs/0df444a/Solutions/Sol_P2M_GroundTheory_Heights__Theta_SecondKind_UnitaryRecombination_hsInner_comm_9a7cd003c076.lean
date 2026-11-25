-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_comm_9a7cd003c076
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:50:16.487647+00:00
-- url     : https://prove2.me/submissions/86ca23de-299b-4279-a194-04846b70badf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_comm_e9aaf395bfd3
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_eq_1ad3b1c0ab1b

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
variable {f : ℕ} {p q : Fin f → ℕ}
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution (X Y : MatProd p q) : hsInner X Y = hsInner Y X := by
  simp only [hsInner_eq, tInner_comm (X _)]
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
