-- Prove2me | solution 1 for PascalExtremes.rP_le_of_lt_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:55:55.133592+00:00
-- url     : https://prove2.me/submissions/ad5a07b8-d8e6-49fc-af4f-028c07bbe2f2

module
public import Mathlib
public import Definitions.Def_PascalExtremes_Powers

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution {p m s : ℕ} (hp : 1 < p) (hm : m ≠ 0)
    (h : m < p ^ s) :
    rP p m ≤ s := by
  have hlog : Nat.log p m < s :=
    (Nat.log_lt_iff_lt_pow hp hm).2 h
  simpa [rP, Nat.succ_le_iff] using hlog
end PascalExtremes
