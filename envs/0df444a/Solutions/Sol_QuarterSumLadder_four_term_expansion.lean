-- Prove2me | solution 1 for QuarterSumLadder.four_term_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:02.997919+00:00
-- url     : https://prove2.me/submissions/4f33e35a-a333-401e-aebd-9cfadd7fd5b2

module
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Definitions.Def_QuarterSumLadder_Arith
public import Definitions.Def_QuarterSumLadder_Ladder
public import Theorems.Thm_QuarterSumLadder_gi_cube
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_gi_sq
public import Theorems.Thm_QuarterSumLadder_sum_R
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
theorem _root_.solution :
    Omega χ = (Q p : GaussianInt) + ((R χ 1 + 2 * R χ 2 + 3 * R χ 3 : ℕ) : GaussianInt) * (gi - 1) +
      ((R χ 2 + 3 * R χ 3 : ℕ) : GaussianInt) * (gi - 1) ^ 2 +
        (R χ 3 : GaussianInt) * (gi - 1) ^ 3 := by
  have hs : (Q p : GaussianInt) = R χ 0 + R χ 1 + R χ 2 + R χ 3 := by
    rw [← sum_R hp8 hχ]; push_cast; ring
  have hO : Omega χ = (R χ 0 : GaussianInt) + R χ 1 * gi + R χ 2 * gi ^ 2 + R χ 3 * gi ^ 3 := by
    rw [gi_sq, gi_cube]; ext <;> simp [Omega, gi] <;> ring
  rw [hO, hs]; push_cast; ring
end QuarterSumLadder
