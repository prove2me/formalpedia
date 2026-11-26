-- Prove2me | solution 1 for QuarterSumLadder.sq_mod_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:09:22.047151+00:00
-- url     : https://prove2.me/submissions/378414b8-c3bb-466c-86b7-493f5eeee1f4

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution (v : ℕ) :
    (((v : ℤ) ^ 2 : ℤ) : ZMod 8) = (if v % 2 = 1 then 1 else 0) + 4 * (if v % 4 = 2 then 1 else 0) := by
  have h : ((v : ℤ) : ZMod 8) = ((v % 8 : ℕ) : ZMod 8) := by
    rw [Int.cast_natCast, ZMod.natCast_mod]
  have h2 : v % 2 = v % 8 % 2 := (Nat.mod_mod_of_dvd v (by norm_num)).symm
  have h4 : v % 4 = v % 8 % 4 := (Nat.mod_mod_of_dvd v (by norm_num)).symm
  push_cast
  rw [show ((v : ZMod 8)) = ((v % 8 : ℕ) : ZMod 8) by rw [ZMod.natCast_mod], h2, h4]
  have hlt := Nat.mod_lt v (show 0 < 8 by norm_num)
  interval_cases (v % 8) <;> decide
end QuarterSumLadder
