-- Prove2me | solution 1 for PI.GTNum.abs_factor_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:43.497449+00:00
-- url     : https://prove2.me/submissions/8093c851-4405-49a2-a644-7febb2184b2d

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
theorem _root_.solution (v s L S : ℤ) (i j n : ℕ) (hi : i < n) (hj : j < n)
    (hv1 : L ≤ v) (hv2 : v ≤ S + (S - L)) (hs1 : L ≤ s) (hs2 : s ≤ S) :
    |v - (i : ℤ) - s + (j : ℤ)| ≤ 2 * (S - L) + ((n + 1 : ℕ) : ℤ) := by
  rw [abs_le]
  push_cast
  constructor <;> omega
end PI.GTNum
