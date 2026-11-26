-- Prove2me | solution 1 for QuarterSumLadder.fourVal_mul_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:10:27.604348+00:00
-- url     : https://prove2.me/submissions/0121b87a-b546-4e8e-b99a-b391145ee5eb

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Theorems.Thm_QuarterSumLadder_char_two
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
namespace QuarterSumLadder
theorem _root_.solution {z : GaussianInt} (hz : FourVal z) : FourVal (χ 2 * z) := by
  rcases char_two hp8 hχ with h | h <;> rw [h] <;> rcases hz with rfl | rfl | rfl | rfl <;>
    simp [FourVal]
end QuarterSumLadder
