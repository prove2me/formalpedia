-- Prove2me | solution 1 for QuarterSumLadder.weight_two_comparison
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:20:01.947934+00:00
-- url     : https://prove2.me/submissions/cad3f749-1c1c-4974-8666-22047225b88e

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
public import Theorems.Thm_QuarterSumLadder_comparison


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (p : ℤ) * (c0 χ - c1 χ) ≡ -4 * ((Omega χ).re - (Omega χ).im) [ZMOD 16] :=
  comparison hp8 hχ
end QuarterSumLadder
