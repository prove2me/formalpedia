-- Prove2me | solution 1 for QuarterSumLadder.quarter_sum_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:18:53.265747+00:00
-- url     : https://prove2.me/submissions/31c0adb6-c978-4d3f-957f-2d44b2f4174c

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
public import Theorems.Thm_QuarterSumLadder_four_term_expansion


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    Omega χ = (Q p : GaussianInt) + ((R χ 1 + 2 * R χ 2 + 3 * R χ 3 : ℕ) : GaussianInt) * (gi - 1) +
      ((R χ 2 + 3 * R χ 3 : ℕ) : GaussianInt) * (gi - 1) ^ 2 +
        (R χ 3 : GaussianInt) * (gi - 1) ^ 3 :=
  four_term_expansion hp8 hχ
end QuarterSumLadder
