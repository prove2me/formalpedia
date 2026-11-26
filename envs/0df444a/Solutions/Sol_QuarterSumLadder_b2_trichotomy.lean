-- Prove2me | solution 1 for QuarterSumLadder.b2_trichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:17:53.923331+00:00
-- url     : https://prove2.me/submissions/440b18fe-4638-4759-9e36-32ad9edf0c2a

module
public import Definitions.Def_QuarterSumLadder_Ladder
public import Definitions.Def_QuarterSumLadder_Boundary
public import Theorems.Thm_QuarterSumLadder_comparison
public import Theorems.Thm_QuarterSumLadder_coord_parity
public import Theorems.Thm_QuarterSumLadder_coords_mod_eight
public import Theorems.Thm_QuarterSumLadder_mod_eight_aux
public import Theorems.Thm_QuarterSumLadder_norm_eq
public import Theorems.Thm_QuarterSumLadder_quarter_law
public import Theorems.Thm_QuarterSumLadder_sq_add_sq_odd
public import Theorems.Thm_QuarterSumLadder_sq_mod_two


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
    (χ 2 = -1 → (32 : ℤ) ∣ (B2 χ).norm ∧ ¬ (64 : ℤ) ∣ (B2 χ).norm) ∧
      (χ 2 = 1 → p % 16 = 9 → (64 : ℤ) ∣ (B2 χ).norm ∧ ¬ (128 : ℤ) ∣ (B2 χ).norm) ∧
      (χ 2 = 1 → p % 16 = 1 → (128 : ℤ) ∣ (B2 χ).norm) := by
  obtain ⟨h0, h1⟩ := coords_mod_eight hp8 hχ
  have hq := quarter_law hp8 hχ
  have hnorm : (B2 χ).norm = c0 χ ^ 2 + c1 χ ^ 2 := norm_eq _
  rw [Int.ModEq] at h0 h1
  rw [hnorm]
  refine ⟨fun hw => ?_, fun hw h16 => ?_, fun hw h16 => ?_⟩
  · rw [hw] at hq
    have hodd : Odd (R χ 1 + R χ 3) := by
      rcases Nat.even_or_odd (R χ 1 + R χ 3) with he | ho
      · rw [he.neg_one_pow] at hq; exact absurd hq (by decide)
      · exact ho
    obtain ⟨k, hk⟩ := hodd
    have hk' : ((R χ 1 + R χ 3 : ℕ) : ℤ) = 2 * k + 1 := by exact_mod_cast hk
    push_cast at hk'
    obtain ⟨a, ha⟩ : ∃ a, c0 χ = 4 * a ∧ a % 2 = 1 := ⟨c0 χ / 4, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, c1 χ = 4 * b ∧ b % 2 = 1 := ⟨c1 χ / 4, by omega⟩
    rw [ha.1, hb.1, show (4 * a) ^ 2 + (4 * b) ^ 2 = 16 * (a ^ 2 + b ^ 2) by ring]
    have := sq_add_sq_odd ha.2 hb.2
    omega
  · rw [hw] at hq
    have heven : Even (R χ 1 + R χ 3) := by
      rcases Nat.even_or_odd (R χ 1 + R χ 3) with he | ho
      · exact he
      · rw [ho.neg_one_pow] at hq; exact absurd hq (by decide)
    obtain ⟨k, hk⟩ := heven
    have hk' : ((R χ 1 + R χ 3 : ℕ) : ℤ) = k + k := by exact_mod_cast hk
    push_cast at hk'
    obtain ⟨a, ha⟩ : ∃ a, c0 χ = 8 * a := ⟨c0 χ / 8, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, c1 χ = 8 * b := ⟨c1 χ / 8, by omega⟩
    have hcmp := comparison hp8 hχ
    obtain ⟨_, _, hxy⟩ := (coord_parity hp8 hχ).2 hw
    have hpq := mod_eight_aux hp8
    have hQ : (Q p : ℤ) % 4 = 2 := by unfold Q; omega
    rw [Int.ModEq, ha, hb] at hcmp
    obtain ⟨t, ht⟩ : ∃ t, (p : ℤ) = 8 * t + 1 := ⟨(p : ℤ) / 8, by omega⟩
    rw [ht] at hcmp
    have hc : (8 * t + 1) * (8 * a - 8 * b) = 8 * (a - b) + 64 * (t * (a - b)) := by ring
    rw [hc] at hcmp
    rw [ha, hb, show (8 * a) ^ 2 + (8 * b) ^ 2 = 64 * (a ^ 2 + b ^ 2) by ring]
    have h1 := sq_mod_two a; have h2 := sq_mod_two b
    refine ⟨dvd_mul_right 64 _, fun h => ?_⟩
    omega
  · rw [hw] at hq
    have heven : Even (R χ 1 + R χ 3) := by
      rcases Nat.even_or_odd (R χ 1 + R χ 3) with he | ho
      · exact he
      · rw [ho.neg_one_pow] at hq; exact absurd hq (by decide)
    obtain ⟨k, hk⟩ := heven
    have hk' : ((R χ 1 + R χ 3 : ℕ) : ℤ) = k + k := by exact_mod_cast hk
    push_cast at hk'
    obtain ⟨a, ha⟩ : ∃ a, c0 χ = 8 * a := ⟨c0 χ / 8, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, c1 χ = 8 * b := ⟨c1 χ / 8, by omega⟩
    have hcmp := comparison hp8 hχ
    obtain ⟨_, _, hxy⟩ := (coord_parity hp8 hχ).2 hw
    have hpq := mod_eight_aux hp8
    have hQ : (Q p : ℤ) % 4 = 0 := by unfold Q; omega
    rw [Int.ModEq, ha, hb] at hcmp
    obtain ⟨t, ht⟩ : ∃ t, (p : ℤ) = 8 * t + 1 := ⟨(p : ℤ) / 8, by omega⟩
    rw [ht] at hcmp
    have hc : (8 * t + 1) * (8 * a - 8 * b) = 8 * (a - b) + 64 * (t * (a - b)) := by ring
    rw [hc] at hcmp
    rw [ha, hb, show (8 * a) ^ 2 + (8 * b) ^ 2 = 64 * (a ^ 2 + b ^ 2) by ring]
    have h1 := sq_mod_two a; have h2 := sq_mod_two b
    omega
end QuarterSumLadder
