-- Prove2me | solution 1 for ULHC.MP.minPath_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:03:44.340877+00:00
-- url     : https://prove2.me/submissions/657401dc-2664-4c8a-a1df-c25cb03c13eb

import Mathlib
import Definitions.Def_ULHC_MinPath
import Theorems.Thm_ULHC_MP_minPathL_none

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]
variable {β : Type} [LinearOrder β] (N : Finset β) (src mid tgt : β → Bool)
  (edge : β → β → Bool) (w : β → ℕ)
namespace ULHC.MP
theorem _root_.solution (h : minPath N src mid tgt edge w = none)
    (q : List β) (hq : IsPath src mid tgt edge q) (hqN : ∀ x ∈ q, x ∈ N) : False :=
  minPathL_none _ _ _ _ _ _ h q hq (fun x hx => by simpa using hqN x hx)
end ULHC.MP
