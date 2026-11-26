-- Prove2me | solution 1 for QuarterSumLadder.weight_two_mod_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:18:00.756637+00:00
-- url     : https://prove2.me/submissions/56035564-be09-4560-8c8c-b3f0ffc21390

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
public import Theorems.Thm_QuarterSumLadder_coords_mod_eight
public import Theorems.Thm_QuarterSumLadder_mod_eight_criterion


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    ((8 : ℤ) ∣ c0 χ ∧ (8 : ℤ) ∣ c1 χ ↔ χ 2 = 1) ∧ (χ 2 = 1 ↔ ∃ y : ZMod p, y ^ 4 = 2) ∧
      c0 χ ≡ 4 * (R χ 1 + R χ 3) [ZMOD 8] ∧ c1 χ ≡ 4 * (R χ 1 + R χ 3) [ZMOD 8] :=
  ⟨(mod_eight_criterion hp8 hχ).1, (mod_eight_criterion hp8 hχ).2, coords_mod_eight hp8 hχ⟩
end QuarterSumLadder
