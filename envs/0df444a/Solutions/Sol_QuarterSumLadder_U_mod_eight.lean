-- Prove2me | solution 1 for QuarterSumLadder.U_mod_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:10:16.714117+00:00
-- url     : https://prove2.me/submissions/e964cfb9-3576-49fc-8595-b3ca7ace5953

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Theorems.Thm_QuarterSumLadder_sq_mod_eight

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
    ((U χ z : ℤ) : ZMod 8) =
      (((fiber χ z).filter fun x => x.val % 2 = 1).card : ZMod 8) + 4 * (E χ z : ZMod 8) := by
  unfold U E
  rw [Int.cast_sum, sum_congr rfl (fun x _ => sq_mod_eight x.val), sum_add_distrib, ← mul_sum,
    sum_boole, sum_boole]
end QuarterSumLadder
