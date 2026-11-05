-- Prove2me | solution 1 for UniformInK.stThrU
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:20:50.976188+00:00
-- url     : https://prove2.me/submissions/ee175be8-4348-42d6-826c-6253a6394602

import Definitions.Def_UniformInK_Spars_Defs
import Mathlib.Tactic.Ring
import Definitions.Def_UniformInK_Spars_Thresholds
set_option autoImplicit false
section
section
open UniformInK
open Finset

namespace UniformInK.Thresholds

private theorem thetaU_pos' {τ : ℕ} (hτ : 0 < τ) (i : ℕ) : 0 < thetaU τ i := by
  cases i with
  | zero => exact Nat.one_pos
  | succ i => exact Nat.mul_pos (by omega) (Nat.pow_pos hτ)

private theorem mul_betaSU_le' (τ r : ℕ) : τ * betaSU τ r ≤ thetaU τ r := by
  cases r with
  | zero => simp [betaSU]
  | succ r => exact le_of_eq (by simp only [betaSU, thetaU]; ring)

private theorem term_eq' (τ : ℕ) {i j : ℕ} (hj : j ≤ i) :
    2 * thetaU τ (i + 2 - (j + 1)) * betaSU τ (j + 1) = 32 * τ ^ (2 * i + 1) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hj
  have h : j + c + 2 - (j + 1) = c + 1 := by omega
  rw [h]
  simp only [betaSU, thetaU]
  ring

private theorem sum_eq' (τ i : ℕ) :
    ∑ i' ∈ range (i + 2), 2 * thetaU τ (i + 2 - i') * betaSU τ i' = 32 * (i + 1) * τ ^ (2 * i + 1) := by
  rw [sum_range_succ', sum_congr rfl fun j hj => term_eq' τ (Nat.lt_succ_iff.1 (mem_range.1 hj)), sum_const, card_range, smul_eq_mul]
  simp only [betaSU, Nat.succ_eq_add_one]
  ring

private theorem step_le' {τ i : ℕ} (hi : 0 < i) (hτ : 8 * i ≤ τ + 4) :
    4 * thetaU τ (i - 1) + ∑ i' ∈ range i, 2 * thetaU τ (i - i') * betaSU τ i' ≤ betaSU τ i := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  cases i with
  | zero => simp [betaSU, thetaU]
  | succ i =>
    rw [sum_eq']
    have h : i + 1 + 1 - 1 = i + 1 := rfl
    rw [h]
    simp only [betaSU, thetaU]
    calc
      4 * (4 * τ ^ (2 * i + 1)) + 32 * (i + 1) * τ ^ (2 * i + 1) = 4 * ((8 * i + 12) * τ ^ (2 * i + 1)) := by ring
      _ ≤ 4 * (τ * τ ^ (2 * i + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ = 4 * τ ^ (2 * (i + 1)) := by ring

end UniformInK.Thresholds

theorem solution : StThrU := fun k τ hk hτ =>
  { pos := UniformInK.Thresholds.thetaU_pos' (by omega)
    step := fun _ hi hik => UniformInK.Thresholds.step_le' hi (by omega)
    mul := UniformInK.Thresholds.mul_betaSU_le' τ }
