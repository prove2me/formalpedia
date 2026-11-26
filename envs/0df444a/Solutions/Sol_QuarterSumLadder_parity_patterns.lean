-- Prove2me | solution 1 for QuarterSumLadder.parity_patterns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:18:49.049218+00:00
-- url     : https://prove2.me/submissions/8b0ef6fb-4e18-477b-b91f-62e5bdee7419

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
public import Theorems.Thm_QuarterSumLadder_patterns_excluded


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    ¬ (R χ 0 % 2 = 1 ∧ R χ 1 % 2 = 0 ∧ R χ 2 % 2 = 1 ∧ R χ 3 % 2 = 0) ∧
      ¬ (R χ 0 % 2 = 0 ∧ R χ 1 % 2 = 1 ∧ R χ 2 % 2 = 0 ∧ R χ 3 % 2 = 1) :=
  patterns_excluded hp8 hχ
end QuarterSumLadder
