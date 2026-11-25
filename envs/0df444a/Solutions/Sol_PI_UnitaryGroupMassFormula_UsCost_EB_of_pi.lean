-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.EB_of_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:00:34.50412+00:00
-- url     : https://prove2.me/submissions/da7495ff-aeca-4a80-98da-81a88e5ecceb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Letters

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
theorem _root_.solution {p s : ℕ} (b : Fin p → Fin s → ℂ) : EB (Matrix.of b) (1 + ‖b‖) := by
  intro i j
  simp only [Matrix.of_apply]
  exact ((norm_le_pi_norm (b i) j).trans (norm_le_pi_norm b i)).trans
    (le_add_of_nonneg_left zero_le_one)
end PI.UnitaryGroupMassFormula.UsCost
