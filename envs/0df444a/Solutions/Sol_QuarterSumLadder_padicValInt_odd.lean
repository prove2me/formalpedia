-- Prove2me | solution 1 for QuarterSumLadder.padicValInt_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:58:03.65564+00:00
-- url     : https://prove2.me/submissions/ceea8a2e-0a70-47f2-82d7-69cff6faef74

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
namespace QuarterSumLadder
theorem _root_.solution {a : ℤ} (ha : a % 2 = 1) : padicValInt 2 a = 0 :=
  padicValInt.eq_zero_of_not_dvd (by push_cast; omega)
end QuarterSumLadder
