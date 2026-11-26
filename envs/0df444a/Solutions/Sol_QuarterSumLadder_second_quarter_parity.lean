-- Prove2me | solution 1 for QuarterSumLadder.second_quarter_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:19:31.76246+00:00
-- url     : https://prove2.me/submissions/122dcc17-05a0-4103-97df-88c0d5fd7630

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
public import Theorems.Thm_QuarterSumLadder_R_two_parity
public import Theorems.Thm_QuarterSumLadder_parity_rho


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) (hw : χ 2 = 1) :
    R χ 2 % 2 = ((p - 1) / 8 + if (2 : ZMod p) ^ ((p - 1) / 8) = -1 then 1 else 0) % 2 ∧
      (if (2 : ZMod p) ^ ((p - 1) / 8) = -1 then 1 else 0) % 2 =
        (if 2 ∣ orderOf (2 : ZMod p) then (p - 1) / (4 * orderOf (2 : ZMod p)) else 0) % 2 :=
  ⟨R_two_parity hp8 hχ hw, parity_rho hp8 hχ hw⟩
end QuarterSumLadder
