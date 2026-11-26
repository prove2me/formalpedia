-- Prove2me | solution 1 for QuarterSumLadder.padicValInt_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:58:02.604849+00:00
-- url     : https://prove2.me/submissions/b1a048da-0348-468b-b81d-b63039d84da5

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
namespace QuarterSumLadder
theorem _root_.solution {a : ℤ} (ha : a ≠ 0) : padicValInt 2 (2 * a) = padicValInt 2 a + 1 := by
  rw [mul_comm]; exact_mod_cast padicValInt_mul_eq_succ (p := 2) a ha
end QuarterSumLadder
