-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_sum_right_e2ea2b48ebbe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:42:58.00361+00:00
-- url     : https://prove2.me/submissions/2cc8f154-422e-45a8-8058-d0345c92aef1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInnerR_apply_d6ec03973d4a

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
variable {ι : Type*} [Fintype ι]
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution {κ : Type*} (s : Finset κ) (X : Matrix ι ι ℂ) (c : κ → ℝ)
    (Y : κ → Matrix ι ι ℂ) : tInner X (∑ m ∈ s, c m • Y m) = ∑ m ∈ s, c m * tInner X (Y m) := by
  rw [← tInnerR_apply, map_sum]
  simp [tInnerR_apply]
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
