-- Prove2me | solution 1 for QuarterSumLadder.sq_add_sq_mixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:56:11.822562+00:00
-- url     : https://prove2.me/submissions/1019e316-c813-4bfa-914c-89ee9cd6ce78

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith
public import Theorems.Thm_QuarterSumLadder_sq_mod_two

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
namespace QuarterSumLadder
theorem _root_.solution {x y : ℤ} (hx : x % 2 = 1) (hy : y % 2 = 0) : (x ^ 2 + y ^ 2) % 2 = 1 := by
  have := sq_mod_two x; have := sq_mod_two y; omega
end QuarterSumLadder
