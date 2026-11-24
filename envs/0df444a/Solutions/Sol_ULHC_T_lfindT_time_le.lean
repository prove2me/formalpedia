-- Prove2me | solution 1 for ULHC.T.lfindT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:25:08.856267+00:00
-- url     : https://prove2.me/submissions/b7b42d8b-8353-433a-9849-ebd6e0c53275

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Timed_TimeM
import Theorems.Thm_ULHC_T_lsum_le

set_option autoImplicit true
open ULHC ULHC.T
open Finset
variable {α β : Type}
namespace ULHC.T
theorem _root_.solution (p : α → TimeM Bool) (l : List α) (c : ℕ) (h : ∀ x ∈ l, (p x).time ≤ c) :
    (lfindT p l).time ≤ l.length * (c + 1) :=
  lsum_le l _ _ (fun x hx => by have := h x hx; omega)
end ULHC.T
