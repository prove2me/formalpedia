-- Prove2me | solution 1 for ULHC.T.filterT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:32:07.330167+00:00
-- url     : https://prove2.me/submissions/cbc25d74-704b-43a4-9a0c-7d87db507f2b

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Timed_TimeM
import Theorems.Thm_ULHC_T_fsum_le

set_option autoImplicit true
open ULHC ULHC.T
open Finset
variable {α β : Type}
namespace ULHC.T
theorem _root_.solution (p : α → TimeM Bool) (s : Finset α) (c : ℕ) (h : ∀ x ∈ s, (p x).time ≤ c) :
    (filterT p s).time ≤ s.card * (c + 1) :=
  fsum_le s _ _ (fun x hx => by have := h x hx; omega)
end ULHC.T
