-- Prove2me | solution 1 for QuarterSumLadder.fourth_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:38.843538+00:00
-- url     : https://prove2.me/submissions/564f06ed-4d0c-4789-8c90-a2a74e75fc75

module
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Definitions.Def_QuarterSumLadder_Arith
public import Definitions.Def_QuarterSumLadder_Ladder
public import Theorems.Thm_QuarterSumLadder_norm_eq
public import Theorems.Thm_QuarterSumLadder_coord_parity
public import Theorems.Thm_QuarterSumLadder_mod_eight_aux
public import Theorems.Thm_QuarterSumLadder_sixteen_dvd_iff
public import Theorems.Thm_QuarterSumLadder_sum_R


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution (hw : χ 2 = 1) (h16 : p % 16 = 1) :
    (16 : ℤ) ∣ (Omega χ).norm ↔ (R χ 1 + 2 * R χ 2 + R χ 3) % 4 = 0 := by
  obtain ⟨hx, hy, hxy⟩ := (coord_parity hp8 hχ).2 hw
  have hs := sum_R hp8 hχ
  have hpq := mod_eight_aux hp8
  have hQ : (Q p : ℤ) % 4 = 0 := by unfold Q; omega
  rw [norm_eq, sixteen_dvd_iff]
  have hre : (Omega χ).re = (R χ 0 : ℤ) - R χ 2 := rfl
  rw [hre] at hx hxy ⊢
  omega
end QuarterSumLadder
