-- Prove2me | solution 1 for QuarterSumLadder.quartic_gauss_lemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:18:03.307804+00:00
-- url     : https://prove2.me/submissions/1920310d-1288-421f-b76c-00ed118585ee

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
public import Theorems.Thm_QuarterSumLadder_quarter_law
public import Theorems.Thm_QuarterSumLadder_two_pow_Q


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (2 : ZMod p) ^ Q p = (-1) ^ (R χ 1 + R χ 3) ∧ χ 2 = (-1) ^ (R χ 1 + R χ 3) :=
  ⟨two_pow_Q hp8 hχ, quarter_law hp8 hχ⟩
end QuarterSumLadder
