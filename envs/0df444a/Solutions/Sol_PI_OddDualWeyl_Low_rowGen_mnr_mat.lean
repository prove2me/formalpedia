-- Prove2me | solution 1 for PI.OddDualWeyl.Low.rowGen_mnr_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:05:36.318828+00:00
-- url     : https://prove2.me/submissions/fbfb6be9-b2ab-461b-a6c8-68bb8a827c0d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Theorems.Thm_PI_OddDualWeyl_Low_rowGen_X

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
theorem _root_.solution {k n : ℕ} (h : n ≤ k) (a b : Fin k) (ρ : Fin n → Fin k) :
    rowGen R a b (mnr R h ρ) = (Matrix.of fun p q : Fin n =>
      Polynomial.C (X (ρ p, Fin.castLE h q) : MvPolynomial (Fin k × Fin k) R) +
      (if ρ p = b then Polynomial.X * Polynomial.C (X (a, Fin.castLE h q)) else 0)).det := by
  rw [mnr, AlgHom.map_det]
  congr 1
  ext p q
  simp [rowGen_X]
end PI.OddDualWeyl.Low
