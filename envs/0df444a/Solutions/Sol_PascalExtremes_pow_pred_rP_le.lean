-- Prove2me | solution 1 for PascalExtremes.pow_pred_rP_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:56:07.271807+00:00
-- url     : https://prove2.me/submissions/036e677f-7e41-44ce-a115-d02671b54479

module
public import Mathlib
public import Definitions.Def_PascalExtremes_Powers

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution {p m : ℕ} (hm : m ≠ 0) :
    p ^ (rP p m - 1) ≤ m := by
  simpa [rP] using Nat.pow_log_le_self p hm
end PascalExtremes
