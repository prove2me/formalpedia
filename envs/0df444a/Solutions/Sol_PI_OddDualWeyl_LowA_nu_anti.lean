-- Prove2me | solution 1 for PI.OddDualWeyl.LowA.nu_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:59:22.663357+00:00
-- url     : https://prove2.me/submissions/00fabcef-cca4-4ee0-a292-8ae2ad592492

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightDualOf

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
open PI PI.OddDualWeyl PI.OddDualWeyl.LowA
variable {R : Type*} [CommRing R]
namespace PI.OddDualWeyl.LowA
theorem _root_.solution {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (t : Fin m) :
    nuOf lam t.succ ≤ nuOf lam t.castSucc := by
  have h := hlam (show t.castSucc ≤ t.succ from Fin.castSucc_lt_succ.le)
  exact Int.toNat_le_toNat (by omega)
end PI.OddDualWeyl.LowA
