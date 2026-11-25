-- Prove2me | solution 1 for PI.StabSplit.UnipW.star_sgn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:28:22.315886+00:00
-- url     : https://prove2.me/submissions/c685c32b-7e9a-442f-b2c5-387032ba41a0

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
theorem _root_.solution {k r : ℕ} (i : Fin (2 * r + k + 1)) : star (sgn k r i) = sgn k r i := by
  unfold sgn
  split_ifs <;> simp
end PI.StabSplit.UnipW
