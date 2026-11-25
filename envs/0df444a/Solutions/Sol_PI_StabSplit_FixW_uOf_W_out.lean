-- Prove2me | solution 1 for PI.StabSplit.FixW.uOf_W_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:27:36.142695+00:00
-- url     : https://prove2.me/submissions/0dd6ddb1-9f2f-4cb7-8754-584a08d5a864

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_FixSub
import Theorems.Thm_PI_StabSplit_FixW_uOf_out_col

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
open PI PI.StabSplit PI.StabSplit.FixW
namespace PI.StabSplit.FixW
theorem _root_.solution {k r : ℕ} (g : B.Mat k r) (i j : Fin (2 * r + k + 1))
    (hi1 : r ≤ i.val) (hi2 : i.val ≤ r + k) (hj : j.val < r ∨ r + k < j.val) :
    uOf k r g i j = 0 := by
  rw [uOf_out_col g i j hj, if_neg]
  intro h; subst h; omega
end PI.StabSplit.FixW
