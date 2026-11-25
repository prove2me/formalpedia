-- Prove2me | solution 1 for PI.GTNum.sum_range_le_tele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:04.527817+00:00
-- url     : https://prove2.me/submissions/005bae18-d010-46d7-9ee5-ab6a8f95867c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GTNum
open Finset
namespace PI.GTNum
theorem _root_.solution (n : ℕ) (a t : ℕ → ℤ) (h : ∀ i < n, a i ≤ t i - t (i + 1)) :
    ∑ i ∈ range n, a i ≤ t 0 - t n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h n (by omega)
    linarith
end PI.GTNum
