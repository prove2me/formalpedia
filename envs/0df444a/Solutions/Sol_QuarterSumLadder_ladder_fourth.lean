-- Prove2me | solution 1 for QuarterSumLadder.ladder_fourth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:19:10.563151+00:00
-- url     : https://prove2.me/submissions/6973e316-8b01-4465-b136-f430bc5ff600

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
public import Theorems.Thm_QuarterSumLadder_fourth_threshold


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) (hw : χ 2 = 1)
    (h16 : p % 16 = 1) :
    (16 : ℤ) ∣ (Omega χ).norm ↔ (R χ 1 + 2 * R χ 2 + R χ 3) % 4 = 0 :=
  fourth_threshold hp8 hχ hw h16
end QuarterSumLadder
