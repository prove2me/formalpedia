-- Prove2me | solution 1 for QuarterSumLadder.weight_two_trichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:20:02.666819+00:00
-- url     : https://prove2.me/submissions/299cdc12-36db-4b2e-9297-21c0ae199f2e

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
public import Theorems.Thm_QuarterSumLadder_b2_trichotomy


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (χ 2 = -1 → (32 : ℤ) ∣ (B2 χ).norm ∧ ¬ (64 : ℤ) ∣ (B2 χ).norm) ∧
      (χ 2 = 1 → p % 16 = 9 → (64 : ℤ) ∣ (B2 χ).norm ∧ ¬ (128 : ℤ) ∣ (B2 χ).norm) ∧
      (χ 2 = 1 → p % 16 = 1 → (128 : ℤ) ∣ (B2 χ).norm) :=
  b2_trichotomy hp8 hχ
end QuarterSumLadder
