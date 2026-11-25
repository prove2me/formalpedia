-- Prove2me | solution 1 for PI.TailWork.sum_Ico_tele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:29:26.355453+00:00
-- url     : https://prove2.me/submissions/17c75328-4d30-4e6e-83ca-65a8adf99b2a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.TailWork
open Finset
namespace PI.TailWork
theorem _root_.solution (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Ico a b, (f n - f (n + 1)) = f a - f b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    ring
end PI.TailWork
