-- Prove2me | solution 1 for PI.StabSplit.UnipW.sum_W_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:37.72874+00:00
-- url     : https://prove2.me/submissions/4fbe32c2-9734-4640-b3d5-4cf702a0f5ea

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
theorem _root_.solution {k r : ℕ} (w : Fin (2 * r + k + 1) → ℂ) :
    0 ≤ ∑ i : Fin (2 * r + k + 1), if (r ≤ i.val ∧ i.val ≤ r + k) then Complex.normSq (w i) else 0 := Finset.sum_nonneg fun i _ => by
    split_ifs <;> first | exact Complex.normSq_nonneg _ | exact le_refl _
end PI.StabSplit.UnipW
