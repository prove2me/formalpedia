-- Prove2me | solution 1 for PI.StabSplit.UnipW.sig_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:36:30.330221+00:00
-- url     : https://prove2.me/submissions/85093633-69c3-4ab1-8dbf-6ba16dcebf7b

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
theorem _root_.solution {k r : ℕ} (i : Fin (2 * r + k + 1)) (h : i.val ≤ r + k) : r ≤ (sig k r i).val := by
  unfold sig
  split_ifs with h'
  · show r ≤ 2 * r + k - i.val
    omega
  · push_neg at h'
    exact h'.1
end PI.StabSplit.UnipW
