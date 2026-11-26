-- Prove2me | solution 1 for QuarterSumLadder.quarter_interval_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:18:10.6457+00:00
-- url     : https://prove2.me/submissions/2876d04e-c9be-4998-9b26-1f8cd3fc6da1

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
public import Theorems.Thm_QuarterSumLadder_kappa_criterion
public import Theorems.Thm_QuarterSumLadder_kappa_eq


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    kappa p = (Q p : ℤ) - 2 * (R χ 1 + R χ 3) ∧ (χ 2 = 1 ↔ kappa p % 4 = (Q p : ℤ) % 4) :=
  ⟨kappa_eq hp8 hχ, kappa_criterion hp8 hχ⟩
end QuarterSumLadder
