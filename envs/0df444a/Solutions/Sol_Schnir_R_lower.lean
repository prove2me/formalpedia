-- Prove2me | solution 1 for Schnir.R_lower
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T22:52:06.277985+00:00
-- url     : https://prove2.me/submissions/d68505c2-50a8-422c-93b6-f3cd2c89ceec

import Mathlib
import Definitions.Def_Schnir_defs
import Theorems.Thm_Schnir_first_moment
import Theorems.Thm_Schnir_second_moment

open Finset Real

namespace Schnir

/-- `r s ≤ s`. -/
theorem mom_r_le (s : ℕ) : r s ≤ s := by
  unfold r
  calc _ ≤ (Finset.Icc 1 s).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_range] at hp
        have := hp.2.1.one_lt
        simp only [Finset.mem_Icc]; omega
    _ = s := by simp

/-- `r s = 0` for odd `s`. -/
theorem mom_r_odd (s : ℕ) (hs : ¬ Even s) : r s = 0 := by
  unfold r
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp ⟨hpp, hp2, hqp, hq2⟩
  simp only [Finset.mem_range] at hp
  have h1 := hpp.odd_of_ne_two hp2
  have h2 := hqp.odd_of_ne_two hq2
  have : Even (p + (s - p)) := Odd.add_odd h1 h2
  rw [Nat.add_sub_cancel' (by omega)] at this
  exact hs this

theorem mom_C_nonneg (s : ℕ) : 0 ≤ C s := by
  unfold C
  apply Finset.prod_nonneg
  intro p _
  positivity

/-- `t / (log t)^2` is increasing on `[e^1000, ∞)` (in the form needed). -/
theorem mom_mono (a b : ℝ) (ha : 1000 ≤ a) (hab : a ≤ b) :
    Real.exp a / a ^ 2 ≤ Real.exp b / b ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : b ≤ a * (1 + (b - a) / 2) := by nlinarith
  have h2 : 1 + (b - a) / 2 ≤ Real.exp ((b - a) / 2) := by
    have := Real.add_one_le_exp ((b - a) / 2); linarith
  have h3 : b ≤ a * Real.exp ((b - a) / 2) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 ha0.le)
  have h4 : b ^ 2 ≤ a ^ 2 * Real.exp (b - a) := by
    have : Real.exp (b - a) = Real.exp ((b - a) / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [this, ← mul_pow]
    exact pow_le_pow_left₀ hb0.le h3 2
  have h5 : Real.exp b = Real.exp a * Real.exp (b - a) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h5]
  have := Real.exp_pos a
  nlinarith

theorem R_lower (x : ℝ) (hx : Real.exp 2000 ≤ x) :
    x / 69660 ≤ (((Finset.range (⌊x⌋₊ + 1)).filter (fun s => 0 < r s)).card : ℝ) := by
  set F := (Finset.range (⌊x⌋₊ + 1)).filter (fun s => 0 < r s) with hF
  have hx2000 : 2000 ≤ x := by
    have := Real.add_one_le_exp 2000; linarith
  have hxpos : 0 < x := by linarith
  have hu : 2000 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 2000) hx
    rwa [Real.log_exp] at this
  set u := Real.log x
  have hupos : 0 < u := by linarith
  have h1 := first_moment x hx2000
  have h2 := second_moment x hx
  set M1 := ∑ s ∈ Finset.range (⌊x⌋₊ + 1), (r s : ℝ)
  set M2 := ∑ s ∈ Finset.range (⌊x⌋₊ + 1), (r s : ℝ) ^ 2
  have hM1F : M1 = ∑ s ∈ F, (r s : ℝ) := by
    rw [hF, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs with h
    · rfl
    · simp at h; simp [h]
  have hM2F : ∑ s ∈ F, (r s : ℝ) ^ 2 ≤ M2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intros; positivity
  have hCS : M1 ^ 2 ≤ (F.card : ℝ) * M2 := by
    rw [hM1F]
    exact (sq_sum_le_card_mul_sum_sq).trans (by gcongr)
  have hA : 0 < x ^ 2 / (9 * u ^ 2) := by positivity
  have hB : (x ^ 2 / (9 * u ^ 2)) ^ 2 ≤ M1 ^ 2 := pow_le_pow_left₀ hA.le h1 2
  have hM2pos : 0 < M2 := by
    rcases (Nat.cast_nonneg F.card : (0:ℝ) ≤ F.card).lt_or_eq with h | h
    · nlinarith
    · rw [← h] at hCS; nlinarith
  have hkey : x / 69660 * M2 ≤ F.card * M2 := by
    calc x / 69660 * M2 ≤ x / 69660 * (860 * x ^ 3 / u ^ 4) := by gcongr
      _ = (x ^ 2 / (9 * u ^ 2)) ^ 2 := by field_simp; ring
      _ ≤ _ := hB.trans hCS
  exact le_of_mul_le_mul_right hkey hM2pos
end Schnir

open Schnir in
theorem solution (x : ℝ) (hx : Real.exp 2000 ≤ x) :
    x / 69660 ≤ (((Finset.range (⌊x⌋₊ + 1)).filter (fun s => 0 < r s)).card : ℝ) :=
  Schnir.R_lower x hx
