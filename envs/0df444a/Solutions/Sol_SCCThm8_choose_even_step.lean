-- Prove2me | solution 1 for SCCThm8.choose_even_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:04.038988+00:00
-- url     : https://prove2.me/submissions/bd361f62-753f-48f7-acb2-e7a6276ca270

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
namespace SCCThm8
theorem _root_.solution (m : ℕ) :
    Nat.choose (2 * m + 2) (m + 1) = 2 * Nat.choose (2 * m + 1) m := by
  rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring, Nat.choose_succ_succ', Nat.choose_symm_half]
  ring
end SCCThm8
