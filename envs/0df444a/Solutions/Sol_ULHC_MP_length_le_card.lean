-- Prove2me | solution 1 for ULHC.MP.length_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:12:24.281313+00:00
-- url     : https://prove2.me/submissions/3c4e7fa1-ce62-4ff0-9307-c5adacb12832

import Mathlib
import Definitions.Def_ULHC_MinPath

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}
namespace ULHC.MP
theorem _root_.solution [DecidableEq α] {NL : List α} {l : List α} (hnd : l.Nodup)
    (hN : ∀ z ∈ l, z ∈ NL) : l.length ≤ NL.length := by
  rw [← List.toFinset_card_of_nodup hnd]
  exact (Finset.card_le_card (fun z hz => List.mem_toFinset.2 (hN z (List.mem_toFinset.1 hz)))).trans
    (List.toFinset_card_le NL)
end ULHC.MP
