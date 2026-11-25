-- Prove2me | solution 1 for PI.OddDualWeyl.Low.pMinor_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:59:00.163404+00:00
-- url     : https://prove2.me/submissions/f0d5025f-b65d-40bc-a8f8-4035cf264a34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero

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
open PI PI.OddDualWeyl PI.OddDualWeyl.Low
variable {R : Type*} [CommRing R]
namespace PI.OddDualWeyl.Low
theorem _root_.solution {k : ℕ} (σ : Equiv.Perm (Fin k)) {n n' : ℕ} (e : n = n') (h : n ≤ k) (h' : n' ≤ k) :
    pMinor R σ n h = pMinor R σ n' h' := by
  subst e; rfl
end PI.OddDualWeyl.Low
