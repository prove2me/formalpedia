-- Prove2me | solution 1 for ULHC.T.allT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:32:13.206449+00:00
-- url     : https://prove2.me/submissions/c2741c4f-5e04-4eb1-9ef7-4f25a2fb3fe0

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Timed_TimeM
import Theorems.Thm_ULHC_T_fsum_le

set_option autoImplicit true
open ULHC ULHC.T
open Finset
variable {α β : Type}
namespace ULHC.T
theorem _root_.solution (p : α → TimeM Bool) (s : Finset α) (c : ℕ) (h : ∀ x ∈ s, (p x).time ≤ c) :
    (allT p s).time ≤ s.card * (c + 1) :=
  fsum_le s _ _ (fun x hx => by have := h x hx; omega)
end ULHC.T
