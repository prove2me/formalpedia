-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_finrank_u_edc412419c4e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:43:02.265483+00:00
-- url     : https://prove2.me/submissions/c22b5d40-9d7e-40ba-801d-1bc300bb5c93

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
variable (p q : ℕ)
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution : Module.finrank ℝ (indefiniteUnitaryLieAlgebra p q) = (p + q) ^ 2 := by
  have h := (matEquivU p q).finrank_eq
  rw [Module.finrank_prod, Module.finrank_matrix, Complex.finrank_real_complex] at h
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  nlinarith [h]
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
