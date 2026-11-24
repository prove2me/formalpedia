-- Prove2me | solution 1 for ULHC.MP.minPath_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:03:53.954459+00:00
-- url     : https://prove2.me/submissions/df9e2072-adbe-40e2-8826-38e41c7edfad

import Mathlib
import Definitions.Def_ULHC_MinPath
import Theorems.Thm_ULHC_MP_minPathL_min

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]
variable {β : Type} [LinearOrder β] (N : Finset β) (src mid tgt : β → Bool)
  (edge : β → β → Bool) (w : β → ℕ)
namespace ULHC.MP
theorem _root_.solution {p : List β} (h : minPath N src mid tgt edge w = some p)
    (q : List β) (hq : IsPath src mid tgt edge q) (hqN : ∀ x ∈ q, x ∈ N) :
    pw w p ≤ pw w q :=
  minPathL_min _ _ _ _ _ _ h q hq (fun x hx => by simpa using hqN x hx)
end ULHC.MP
