-- Prove2me | solution 1 for QuarterSumLadder.ladder_bottom_valuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:18:58.297217+00:00
-- url     : https://prove2.me/submissions/7ce854a8-aa71-480b-b5e5-a40a6fb37c7f

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
public import Theorems.Thm_QuarterSumLadder_vlam_Omega


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (χ 2 = -1 → vlam (Omega χ) = 1) ∧ (χ 2 = 1 → p % 16 = 9 → vlam (Omega χ) = 2) ∧
      (χ 2 = 1 → p % 16 = 1 → Omega χ ≠ 0 → 3 ≤ vlam (Omega χ)) :=
  vlam_Omega hp8 hχ
end QuarterSumLadder
