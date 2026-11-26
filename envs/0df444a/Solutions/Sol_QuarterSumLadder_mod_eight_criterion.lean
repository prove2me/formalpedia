-- Prove2me | solution 1 for QuarterSumLadder.mod_eight_criterion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:15:55.714803+00:00
-- url     : https://prove2.me/submissions/6845c8b0-6c3c-412b-acb0-6bbb79c459af

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Theorems.Thm_QuarterSumLadder_coords_mod_eight
public import Theorems.Thm_QuarterSumLadder_char_eq_one_iff
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_hp2_of
public import Theorems.Thm_QuarterSumLadder_quarter_law
public import Theorems.Thm_QuarterSumLadder_two_ne_zero_zmod
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
theorem _root_.solution :
    ((8 : ℤ) ∣ c0 χ ∧ (8 : ℤ) ∣ c1 χ ↔ χ 2 = 1) ∧ (χ 2 = 1 ↔ ∃ y : ZMod p, y ^ 4 = 2) := by
  refine ⟨?_, char_eq_one_iff hχ (two_ne_zero_zmod (hp2_of hp8))⟩
  obtain ⟨h0, h1⟩ := coords_mod_eight hp8 hχ
  have hq := quarter_law hp8 hχ
  rw [Int.ModEq] at h0 h1
  rcases Nat.even_or_odd (R χ 1 + R χ 3) with he | ho
  · rw [he.neg_one_pow] at hq
    obtain ⟨k, hk⟩ := he
    have hk' : ((R χ 1 + R χ 3 : ℕ) : ℤ) = k + k := by exact_mod_cast hk
    push_cast at hk'
    simp only [hq, iff_true]
    constructor <;> omega
  · rw [ho.neg_one_pow] at hq
    obtain ⟨k, hk⟩ := ho
    have hk' : ((R χ 1 + R χ 3 : ℕ) : ℤ) = 2 * k + 1 := by exact_mod_cast hk
    push_cast at hk'
    rw [hq]
    simp only [show ((-1 : GaussianInt) = 1) ↔ False by decide, iff_false, not_and]
    omega
end QuarterSumLadder
