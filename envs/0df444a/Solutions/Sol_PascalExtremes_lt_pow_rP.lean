-- Prove2me | solution 1 for PascalExtremes.lt_pow_rP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:55:53.307981+00:00
-- url     : https://prove2.me/submissions/ba4823a9-6fe9-4729-9634-ec6b60f3cc41

module
public import Mathlib
public import Definitions.Def_PascalExtremes_Powers

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution {p m : ℕ} (hp : 1 < p) :
    m < p ^ rP p m := by
  simpa [rP, Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hp m
end PascalExtremes
