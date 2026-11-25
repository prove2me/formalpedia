-- Prove2me | solution 1 for PI.OddDualWeyl.Low.rowGen_mnr_of_not
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:10:57.230657+00:00
-- url     : https://prove2.me/submissions/1a9342ff-e69a-44a6-9ad1-c5a45f352b1c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Theorems.Thm_PI_OddDualWeyl_Low_rowGen_mnr_mat
import Theorems.Thm_PI_OddDualWeyl_Low_C_mnr

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
theorem _root_.solution {k n : ℕ} (h : n ≤ k) (a b : Fin k) (ρ : Fin n → Fin k)
    (hb : ∀ p, ρ p ≠ b) : rowGen R a b (mnr R h ρ) = Polynomial.C (mnr R h ρ) := by
  rw [rowGen_mnr_mat, C_mnr]
  congr 1
  ext p q
  simp [hb p]
end PI.OddDualWeyl.Low
