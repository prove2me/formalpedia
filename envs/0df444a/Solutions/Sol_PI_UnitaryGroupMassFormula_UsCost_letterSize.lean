-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.letterSize
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:55.958682+00:00
-- url     : https://prove2.me/submissions/f34eba85-1cc8-4f3e-aa27-119af73fc222

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Letters
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_lsz_conj_le
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_EB_hat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_Rn_unitary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Ux5
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution : LetterSize := by
  intro k j ρ
  refine ⟨((2 * (j + ρ) + k + 1 : ℕ) : ℝ) ^ 4 * (1 + 1), fun x Y hY => ?_⟩
  have hb : EB (blk3 (0 : Matrix (Fin j) (Fin j) ℂ) 0 0 0 Y 0 0 0 0 : B.Mat k (j + ρ)) 1 := EB_hat Y hY zero_le_one
  exact lsz_conj_le (Rn k j ρ x) _ (Formalism.FourierDecayAlt.P.Ux4.Rn_unitary x) hb zero_le_one
end PI.UnitaryGroupMassFormula.UsCost
