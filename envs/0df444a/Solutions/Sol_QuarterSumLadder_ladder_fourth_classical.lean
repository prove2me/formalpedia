-- Prove2me | solution 1 for QuarterSumLadder.ladder_fourth_classical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:19:29.696881+00:00
-- url     : https://prove2.me/submissions/68df93af-4631-4c5b-aaaa-91b124c1da57

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
public import Theorems.Thm_QuarterSumLadder_fourth_threshold_eval


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) (hw : χ 2 = 1)
    (h16 : p % 16 = 1) :
    (4 : ℤ) ∣ kappa p ∧
      ((16 : ℤ) ∣ (Omega χ).norm ↔
        (((Q p : ℤ) - kappa p) / 4 + ((p - 1) / 8 : ℕ) +
          ((if 2 ∣ orderOf (2 : ZMod p) then (p - 1) / (4 * orderOf (2 : ZMod p)) else 0 : ℕ) :
            ℤ)) % 2 = 0) :=
  fourth_threshold_eval hp8 hχ hw h16
end QuarterSumLadder
