-- Prove2me | solution 1 for PI.GTNum.card_erase_Icc_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:48.22371+00:00
-- url     : https://prove2.me/submissions/d7387874-faf4-406a-8d56-2bf7078df8cc

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
theorem _root_.solution (a b c x : ℤ) (hab : a ≤ b) (hc : 0 ≤ c)
    (hx : x ∈ Icc a (min b (a + c))) :
    ((((Icc a (min b (a + c))).erase x).card : ℕ) : ℤ) = min (b - a) c := by
  rw [Finset.card_erase_of_mem hx, Int.card_Icc]
  have h1 : 1 ≤ (min b (a + c) + 1 - a).toNat := by omega
  rw [Nat.cast_sub h1, Int.toNat_of_nonneg (by omega)]
  push_cast
  omega
end PI.GTNum
