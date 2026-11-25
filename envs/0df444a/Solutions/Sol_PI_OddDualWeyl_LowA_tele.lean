-- Prove2me | solution 1 for PI.OddDualWeyl.LowA.tele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:58:04.084611+00:00
-- url     : https://prove2.me/submissions/c36dae0d-e00d-44ac-b673-5b4fa89f874e

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
theorem _root_.solution (G : ℕ → ℤ) (n : ℕ) :
    ∑ j ∈ Finset.range n, ((n : ℤ) - 1 - j) * (G j - G (j + 1)) =
      n * G 0 - ∑ j ∈ Finset.range n, G j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∀ j ∈ Finset.range (n + 1), (((n + 1 : ℕ) : ℤ) - 1 - j) * (G j - G (j + 1)) =
        ((n : ℤ) - 1 - j) * (G j - G (j + 1)) + (G j - G (j + 1)) := by
      intro j _
      push_cast
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_range_sub', Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    push_cast
    ring
end PI.OddDualWeyl.LowA
