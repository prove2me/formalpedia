-- Prove2me | solution 1 for PI.OddDualWeyl.Low.mnr_update_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:58:55.643428+00:00
-- url     : https://prove2.me/submissions/b10584a2-da08-45a0-aec9-350c52edf3b0

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
theorem _root_.solution {k n : ℕ} (h : n ≤ k) (a : Fin k) (ρ : Fin n → Fin k) (p0 p1 : Fin n)
    (hne : p1 ≠ p0) (hp1 : ρ p1 = a) : mnr R h (Function.update ρ p0 a) = 0 := by
  classical
  rw [mnr]
  apply det_zero_of_row_eq (i := p0) (j := p1) hne.symm
  funext q
  simp [Function.update_of_ne hne, hp1]
end PI.OddDualWeyl.Low
