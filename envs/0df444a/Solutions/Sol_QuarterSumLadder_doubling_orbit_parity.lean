-- Prove2me | solution 1 for QuarterSumLadder.doubling_orbit_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:18:12.292599+00:00
-- url     : https://prove2.me/submissions/6d9bf4cc-a8d9-4e0d-b090-07beea4a2ea1

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
public import Theorems.Thm_QuarterSumLadder_orbit_parity


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) (hw : χ 2 = 1) :
    R χ 1 % 2 = R χ 0 % 2 ∧ R χ 2 % 2 = R χ 0 % 2 ∧ R χ 3 % 2 = R χ 0 % 2 :=
  orbit_parity hp8 hχ hw
end QuarterSumLadder
