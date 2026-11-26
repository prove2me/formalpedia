-- Prove2me | solution 1 for QuarterSumLadder.ladder_bottom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:18:55.266243+00:00
-- url     : https://prove2.me/submissions/580306fc-ea0d-42bc-b7dc-bbb1611d5dd6

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
public import Theorems.Thm_QuarterSumLadder_first_thresholds


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (χ 2 = -1 → (2 : ℤ) ∣ (Omega χ).norm ∧ ¬ (4 : ℤ) ∣ (Omega χ).norm) ∧
      (χ 2 = 1 → p % 16 = 9 → (4 : ℤ) ∣ (Omega χ).norm ∧ ¬ (8 : ℤ) ∣ (Omega χ).norm) ∧
      (χ 2 = 1 → p % 16 = 1 → (8 : ℤ) ∣ (Omega χ).norm) :=
  first_thresholds hp8 hχ
end QuarterSumLadder
