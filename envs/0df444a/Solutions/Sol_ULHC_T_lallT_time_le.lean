-- Prove2me | solution 1 for ULHC.T.lallT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:39:10.286817+00:00
-- url     : https://prove2.me/submissions/5f78b7a2-b479-4160-b85d-b25385a71941

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Timed_TimeM
import Theorems.Thm_ULHC_T_lsum_le

set_option autoImplicit true
open ULHC ULHC.T
open Finset
variable {α β : Type}
namespace ULHC.T
theorem _root_.solution (p : α → TimeM Bool) (l : List α) (c : ℕ) (h : ∀ x ∈ l, (p x).time ≤ c) :
    (lallT p l).time ≤ l.length * (c + 1) :=
  lsum_le l _ _ (fun x hx => by have := h x hx; omega)
end ULHC.T
