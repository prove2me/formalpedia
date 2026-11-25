-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_sum_left_c312c8f11683
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:58:45.971876+00:00
-- url     : https://prove2.me/submissions/67098ded-c210-4e65-8e97-adf99e0719d4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_comm_9a7cd003c076
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_sum_right_420d47d25329

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
theorem _root_.solution {κ : Type*} (s : Finset κ) (X : MatProd p q) (c : κ → ℝ)
    (Y : κ → MatProd p q) : hsInner (∑ m ∈ s, c m • Y m) X = ∑ m ∈ s, c m * hsInner (Y m) X := by
  rw [hsInner_comm, hsInner_sum_right]
  simp [hsInner_comm X]
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
