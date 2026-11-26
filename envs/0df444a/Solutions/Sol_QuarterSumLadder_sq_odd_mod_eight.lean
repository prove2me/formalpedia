-- Prove2me | solution 1 for QuarterSumLadder.sq_odd_mod_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:57:33.272749+00:00
-- url     : https://prove2.me/submissions/28991185-dfae-47b0-b749-5d50ad2596ea

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
namespace QuarterSumLadder
theorem _root_.solution {a : ℤ} (ha : a % 2 = 1) : a ^ 2 % 8 = 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, a = 2 * r + 1 := ⟨a / 2, by omega⟩
  have h : (2 * r + 1) ^ 2 = 4 * (r * (r + 1)) + 1 := by ring
  obtain ⟨s, hs⟩ := Int.even_mul_succ_self r
  rw [h, hs]; omega
end QuarterSumLadder
