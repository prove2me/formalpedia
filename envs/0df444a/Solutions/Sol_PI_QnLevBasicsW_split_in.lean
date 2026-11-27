-- Prove2me | solution 1 for PI.QnLevBasicsW.split_in
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:18:06.659238+00:00
-- url     : https://prove2.me/submissions/809fc1e3-80a8-481f-9df1-e8d56e389706

import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Theorems.Thm_PI_QnLevBasicsW_split_symm_inl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QnLevBasicsW
open Formalism.QuantumDeterminants
variable {k i r' : ℕ}
namespace PI.QnLevBasicsW
theorem _root_.solution (p : Fin (2 * (i + r') + k + 1)) (a : Fin (2 * r' + k + 1)) (h : p.val = a.val + i) :
    split k i r' p = Sum.inl a := by
  apply (split k i r').symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  rw [split_symm_inl]
  exact h
end PI.QnLevBasicsW
