-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_exp_le_cae1f6c984d7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:59.13315+00:00
-- url     : https://prove2.me/submissions/a6fdd22b-006c-41ad-89ab-2c467798a298

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_exp_sub_one_le_bd2115446053

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
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (h1 : ‖(1 : 𝔸)‖ ≤ 1) (x : 𝔸) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  have := norm_exp_sub_one_le x
  calc ‖NormedSpace.exp x‖ = ‖(NormedSpace.exp x - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ ‖NormedSpace.exp x - 1‖ + ‖(1 : 𝔸)‖ := norm_add_le _ _
    _ ≤ Real.exp ‖x‖ := by linarith
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
