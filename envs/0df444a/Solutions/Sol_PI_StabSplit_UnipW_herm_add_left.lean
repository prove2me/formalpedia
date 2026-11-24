-- Prove2me | solution 1 for PI.StabSplit.UnipW.herm_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:13:49.620567+00:00
-- url     : https://prove2.me/submissions/7e2f8738-0e91-47ad-afff-7749dac5c9ff

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_NilpotentOrthogonalComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.StabSplit PI.StabSplit.UnipW
namespace PI.StabSplit.UnipW
theorem _root_.solution {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (a b w : Fin m → ℂ) :
    herm H (a + b) w = herm H a w + herm H b w := by
  unfold herm
  rw [Matrix.mulVec_add, dotProduct_add]
end PI.StabSplit.UnipW
