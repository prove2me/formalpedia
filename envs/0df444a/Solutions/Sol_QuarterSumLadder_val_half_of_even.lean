-- Prove2me | solution 1 for QuarterSumLadder.val_half_of_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:00:41.32588+00:00
-- url     : https://prove2.me/submissions/d60291fd-6add-40fd-b85b-c4ee86d60dda

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes

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
theorem _root_.solution {y : ZMod p} (hy : Even y.val) : (2 * (y.val / 2 : ℕ) : ZMod p) = y := by
  obtain ⟨k, hk⟩ := hy
  rw [show y.val / 2 = k by omega, ← ZMod.natCast_zmod_val y, hk]; push_cast; ring
end QuarterSumLadder
