-- Prove2me | solution 1 for PI.OddDualWeyl.Low.mnr_comp_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:58:51.027429+00:00
-- url     : https://prove2.me/submissions/e4d35fbb-8609-4444-8243-4735a9b7aaa5

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
theorem _root_.solution {k n : ℕ} (h : n ≤ k) (ρ : Fin n → Fin k) (p q : Fin n) (hpq : p ≠ q) :
    mnr R h (ρ ∘ Equiv.swap p q) = - mnr R h ρ := by
  have e : (Matrix.of fun x y : Fin n =>
      (X ((ρ ∘ Equiv.swap p q) x, Fin.castLE h y) : MvPolynomial (Fin k × Fin k) R)) =
      (Matrix.of fun x y : Fin n =>
        (X (ρ x, Fin.castLE h y) : MvPolynomial (Fin k × Fin k) R)).submatrix (Equiv.swap p q) id := by
    ext x y; simp
  rw [mnr, e, det_permute, Equiv.Perm.sign_swap hpq]
  simp [mnr]
end PI.OddDualWeyl.Low
