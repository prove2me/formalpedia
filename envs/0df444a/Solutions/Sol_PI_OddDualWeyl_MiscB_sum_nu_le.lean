-- Prove2me | solution 1 for PI.OddDualWeyl.MiscB.sum_nu_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:59:04.776145+00:00
-- url     : https://prove2.me/submissions/089d5a73-b6e6-4719-8152-1fff635e1548

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_DegreeBalance
import Theorems.Thm_PI_OddDualWeyl_MiscB_nu_anti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open PI.OddDualWeyl.MiscB
variable {m : ℕ} {lam : Fin (m + 1) → ℤ}
namespace PI.OddDualWeyl.MiscB
theorem _root_.solution (hl : Antitone lam) : ∑ t, nuOf lam t ≤ m * nuOf lam 0 := by
  rw [Fin.sum_univ_castSucc]
  have hl0 : nuOf lam (Fin.last m) = 0 := by
    unfold nuOf
    simp
  rw [hl0, add_zero]
  calc ∑ t : Fin m, nuOf lam t.castSucc ≤ ∑ _t : Fin m, nuOf lam 0 :=
        Finset.sum_le_sum fun t _ => nu_anti hl (Fin.zero_le _)
    _ = m * nuOf lam 0 := by simp
end PI.OddDualWeyl.MiscB
