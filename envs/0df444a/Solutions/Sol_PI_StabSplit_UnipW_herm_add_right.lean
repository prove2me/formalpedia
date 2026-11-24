-- Prove2me | solution 1 for PI.StabSplit.UnipW.herm_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:13:51.522575+00:00
-- url     : https://prove2.me/submissions/02bff589-d1e2-448f-ba90-2230c02ed031

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
theorem _root_.solution {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (v a b : Fin m → ℂ) :
    herm H v (a + b) = herm H v a + herm H v b := by
  unfold herm
  rw [star_add, add_dotProduct]
end PI.StabSplit.UnipW
