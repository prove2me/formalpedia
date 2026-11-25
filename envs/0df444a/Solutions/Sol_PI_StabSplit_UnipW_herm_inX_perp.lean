-- Prove2me | solution 1 for PI.StabSplit.UnipW.herm_inX_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:26.341109+00:00
-- url     : https://prove2.me/submissions/52983e6d-ca06-4027-a20e-91abaf191972

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_NilpotentOrthogonalComplement
import Theorems.Thm_PI_StabSplit_UnipW_sig_ge
import Theorems.Thm_PI_StabSplit_UnipW_herm_coord

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
theorem _root_.solution {k r : ℕ} {v x : Fin (2 * r + k + 1) → ℂ} (hv : perpX k r v) (hx : inX k r x) :
    herm (Hpk k r) x v = 0 := by
  rw [herm_coord]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val ≤ r + k
  · rw [hx _ (sig_ge i hi)]
    ring
  · rw [hv i (by omega)]
    simp
end PI.StabSplit.UnipW
