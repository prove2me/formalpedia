-- Prove2me | solution 1 for QuarterSumLadder.sq_add_sq_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:58:30.402857+00:00
-- url     : https://prove2.me/submissions/4099b701-afa6-402c-a827-d640c6483880

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith
public import Theorems.Thm_QuarterSumLadder_sq_odd_mod_eight

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
namespace QuarterSumLadder
theorem _root_.solution {x y : ℤ} (hx : x % 2 = 1) (hy : y % 2 = 1) : (x ^ 2 + y ^ 2) % 8 = 2 := by
  have := sq_odd_mod_eight hx; have := sq_odd_mod_eight hy; omega
end QuarterSumLadder
