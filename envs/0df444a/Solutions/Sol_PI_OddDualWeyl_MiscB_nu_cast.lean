-- Prove2me | solution 1 for PI.OddDualWeyl.MiscB.nu_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:46.892791+00:00
-- url     : https://prove2.me/submissions/2e2b80b2-9396-427f-905a-f3a8c1ad360c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_DegreeBalance

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
theorem _root_.solution (hl : Antitone lam) (t : Fin (m + 1)) : (nuOf lam t : ℤ) = lam t - lam (Fin.last m) := by
  unfold nuOf
  exact Int.toNat_of_nonneg (sub_nonneg.2 (hl (Fin.le_last t)))
end PI.OddDualWeyl.MiscB
