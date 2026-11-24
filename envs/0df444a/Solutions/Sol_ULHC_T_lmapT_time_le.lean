-- Prove2me | solution 1 for ULHC.T.lmapT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:31:09.265009+00:00
-- url     : https://prove2.me/submissions/f730f8dc-b522-42c7-84e4-e958ba58296d

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Timed_TimeM
import Theorems.Thm_ULHC_T_lsum_le

set_option autoImplicit true
open ULHC ULHC.T
open Finset
variable {α β : Type}
namespace ULHC.T
theorem _root_.solution (f : α → TimeM β) (l : List α) (c : ℕ) (h : ∀ x ∈ l, (f x).time ≤ c) :
    (lmapT f l).time ≤ l.length * (c + 1) :=
  lsum_le l _ _ (fun x hx => by have := h x hx; omega)
end ULHC.T
