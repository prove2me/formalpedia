-- Prove2me | solution 1 for QuarterSumLadder.neg_one_pow_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:06:54.303071+00:00
-- url     : https://prove2.me/submissions/da9c23f5-31c1-4eb6-aa38-eb03b0b06567

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
attribute [local simp] QuarterSumLadder.gi_im
attribute [local simp] QuarterSumLadder.gi_re



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
theorem _root_.solution (n : ℕ) : ((-1 : ZMod p) ^ n) * (-1) ^ n = 1 := by
  rw [← mul_pow]; simp
end QuarterSumLadder
