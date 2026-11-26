-- Prove2me | solution 1 for QuarterSumLadder.sq_mod_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:12:29.016175+00:00
-- url     : https://prove2.me/submissions/41a89ec1-8af7-4953-b3a9-10128dc9064a

module
public import Definitions.Def_QuarterSumLadder_Ladder
public import Definitions.Def_QuarterSumLadder_Boundary

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution (v : ℕ) :
    (((v : ℤ) ^ 2 : ℤ) : ZMod 16) = (if v % 2 = 1 then 1 else 0) +
      8 * (if v % 8 = 3 ∨ v % 8 = 5 then 1 else 0) + 4 * (if v % 4 = 2 then 1 else 0) := by
  have h2 : v % 2 = v % 16 % 2 := (Nat.mod_mod_of_dvd v (by norm_num)).symm
  have h4 : v % 4 = v % 16 % 4 := (Nat.mod_mod_of_dvd v (by norm_num)).symm
  have h8 : v % 8 = v % 16 % 8 := (Nat.mod_mod_of_dvd v (by norm_num)).symm
  push_cast
  rw [show ((v : ZMod 16)) = ((v % 16 : ℕ) : ZMod 16) by rw [ZMod.natCast_mod], h2, h4, h8]
  have hlt := Nat.mod_lt v (show 0 < 16 by norm_num)
  interval_cases (v % 16) <;> decide
end QuarterSumLadder
