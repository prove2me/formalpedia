-- Prove2me | solution 1 for PI.OddDualWeyl.Low.castLE_ne_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:45.505479+00:00
-- url     : https://prove2.me/submissions/5d9875f8-22b6-46e2-89b0-ae6071f2eeed

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
variable {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)
namespace PI.OddDualWeyl.Low
theorem _root_.solution {s : ℕ} (h : s ≤ n + 1) (p : Fin s) (j : Fin (n + 1)) (hj : p.val < j.val) :
    Fin.castLE h p ≠ j := by
  intro e; have := congrArg Fin.val e; simp at this; omega
end PI.OddDualWeyl.Low
