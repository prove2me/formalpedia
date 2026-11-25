-- Prove2me | solution 1 for PI.OddDualWeyl.MiscB.abel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:59:00.005387+00:00
-- url     : https://prove2.me/submissions/7e0d93ae-6d21-4b4f-b1c3-80f530dc4f45

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
namespace PI.OddDualWeyl.MiscB
theorem _root_.solution (f : ℕ → ℕ) (hf : ∀ s, f (s + 1) ≤ f s) :
    ∀ n, ∑ s ∈ Finset.range n, (s + 1) * (f s - f (s + 1)) + n * f n = ∑ s ∈ Finset.range n, f s
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← solution f hf n, add_assoc, ← Nat.mul_add,
      Nat.sub_add_cancel (hf n)]
    ring
end PI.OddDualWeyl.MiscB
