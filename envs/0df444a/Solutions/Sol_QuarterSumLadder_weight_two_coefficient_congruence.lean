-- Prove2me | solution 1 for QuarterSumLadder.weight_two_coefficient_congruence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:17:56.719526+00:00
-- url     : https://prove2.me/submissions/d9e76d76-21d9-45a7-9786-0c4d7a52a164

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
public import Theorems.Thm_QuarterSumLadder_weight_two_congruence


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    c0 χ ≡ 4 * (E χ 1 + E χ (-1)) [ZMOD 8] ∧ c1 χ ≡ 4 * (E χ gi + E χ (-gi)) [ZMOD 8] ∧
      c0 χ + c1 χ ≡ p - 1 [ZMOD 8] :=
  weight_two_congruence hp8 hχ
end QuarterSumLadder
