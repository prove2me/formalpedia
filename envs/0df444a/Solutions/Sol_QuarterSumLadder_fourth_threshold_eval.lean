-- Prove2me | solution 1 for QuarterSumLadder.fourth_threshold_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:16:18.353965+00:00
-- url     : https://prove2.me/submissions/9fab9be2-70aa-4367-b681-172d7bf1f185

module
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Definitions.Def_QuarterSumLadder_Arith
public import Definitions.Def_QuarterSumLadder_Ladder
public import Theorems.Thm_QuarterSumLadder_fourth_threshold
public import Theorems.Thm_QuarterSumLadder_R_two_parity
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_kappa_eq
public import Theorems.Thm_QuarterSumLadder_mod_eight_aux
public import Theorems.Thm_QuarterSumLadder_parity_rho
public import Theorems.Thm_QuarterSumLadder_quarter_law
attribute [local simp] QuarterSumLadder.gi_im
attribute [local simp] QuarterSumLadder.gi_re



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
    (4 : ℤ) ∣ kappa p ∧
      ((16 : ℤ) ∣ (Omega χ).norm ↔
        (((Q p : ℤ) - kappa p) / 4 + ((p - 1) / 8 : ℕ) +
          ((if 2 ∣ orderOf (2 : ZMod p) then (p - 1) / (4 * orderOf (2 : ZMod p)) else 0 : ℕ) :
            ℤ)) % 2 = 0) := by
  have hk := kappa_eq hp8 hχ
  have hq := quarter_law hp8 hχ
  rw [hw] at hq
  have heven : Even (R χ 1 + R χ 3) := by
    rcases Nat.even_or_odd (R χ 1 + R χ 3) with he | ho
    · exact he
    · rw [ho.neg_one_pow] at hq; exact absurd hq (by decide)
  obtain ⟨j, hj⟩ := heven
  have hpq := mod_eight_aux hp8
  have hQ : (Q p : ℤ) % 4 = 0 := by unfold Q; omega
  have hR2 := R_two_parity hp8 hχ hw
  have hρ := parity_rho hp8 hχ hw
  have h4 := fourth_threshold hp8 hχ hw h16
  set ι := (if 2 ∣ orderOf (2 : ZMod p) then (p - 1) / (4 * orderOf (2 : ZMod p)) else 0)
  set δ := (if (2 : ZMod p) ^ ((p - 1) / 8) = -1 then 1 else 0)
  have hδ : δ ≤ 1 := by simp only [δ]; split_ifs <;> omega
  refine ⟨⟨((Q p : ℤ) / 4) - j, by rw [hk]; push_cast [hj]; omega⟩, ?_⟩
  rw [h4, hk]
  have : ((Q p : ℤ) - ((Q p : ℤ) - 2 * ((R χ 1 : ℤ) + R χ 3))) / 4 = j := by
    have : ((R χ 1 : ℤ) + R χ 3) = j + j := by exact_mod_cast hj
    rw [this]; omega
  rw [this]
  omega
end QuarterSumLadder
