-- Prove2me | solution 1 for QuarterSumLadder.U_mod_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:10.756065+00:00
-- url     : https://prove2.me/submissions/74e00af8-c229-4c0b-9fbb-23368e084d84

module
public import Definitions.Def_QuarterSumLadder_Ladder
public import Definitions.Def_QuarterSumLadder_Boundary
public import Theorems.Thm_QuarterSumLadder_sq_mod_sixteen

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
omit hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution (z : GaussianInt) :
    ((U χ z : ℤ) : ZMod 16) =
      (((fiber χ z).filter fun x => x.val % 2 = 1).card : ZMod 16) +
        8 * (((fiber χ z).filter fun x => x.val % 8 = 3 ∨ x.val % 8 = 5).card : ZMod 16) +
          4 * (E χ z : ZMod 16) := by
  unfold U E
  rw [Int.cast_sum, sum_congr rfl (fun x _ => sq_mod_sixteen x.val), sum_add_distrib,
    sum_add_distrib, ← mul_sum, ← mul_sum, sum_boole, sum_boole, sum_boole]
end QuarterSumLadder
