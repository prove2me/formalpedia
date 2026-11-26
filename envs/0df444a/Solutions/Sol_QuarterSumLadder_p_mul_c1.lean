-- Prove2me | solution 1 for QuarterSumLadder.p_mul_c1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:09:56.936271+00:00
-- url     : https://prove2.me/submissions/39931ed5-1454-4c79-a128-f0d32f4f8e5a

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Theorems.Thm_QuarterSumLadder_p_dvd_U

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution : (p : ℤ) * c1 χ = U χ gi - U χ (-gi) :=
  Int.mul_ediv_cancel' (dvd_sub (p_dvd_U hp8 hχ) (p_dvd_U hp8 hχ))
end QuarterSumLadder
