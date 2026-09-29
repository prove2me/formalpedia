-- Prove2me | solution 1 for Schnir.second_moment
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T22:52:07.613986+00:00
-- url     : https://prove2.me/submissions/53572b75-31b0-422a-9eb1-d6ec3ee12f27

import Mathlib
import Definitions.Def_Schnir_defs
import Theorems.Thm_Schnir_pointwise_bound
import Theorems.Thm_Schnir_C_mean
import Theorems.Thm_Schnir_first_moment

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

theorem second_moment (x : ℝ) (hx : Real.exp 2000 ≤ x) :
    ∑ s ∈ Finset.range (⌊x⌋₊ + 1), (r s : ℝ) ^ 2 ≤ 860 * x ^ 3 / (Real.log x) ^ 4 := by
  set Y := Real.exp 1000 with hY
  have hYpos : 0 < Y := Real.exp_pos _
  have hY1 : 1001 ≤ Y := by have := Real.add_one_le_exp 1000; linarith
  have hYY : Y * Y = Real.exp 2000 := by rw [hY, ← Real.exp_add]; norm_num
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  set u := Real.log x with hu
  have hu2000 : 2000 ≤ u := by
    have := Real.log_le_log (Real.exp_pos 2000) hx
    rwa [Real.log_exp] at this
  have hxu : Real.exp u = x := Real.exp_log hxpos
  have hupos : 0 < u := by linarith
  set K := 81 * x ^ 2 / u ^ 4 with hK
  -- pointwise bound
  have hpt : ∀ s ∈ Finset.range (⌊x⌋₊ + 1), (r s : ℝ) ^ 2 ≤
      (if (s : ℝ) < Y then Y ^ 2 else 0) +
      (if Even s ∧ 1 ≤ s then K * C s ^ 2 else 0) := by
    intro s hs
    simp only [Finset.mem_range] at hs
    have hsx : (s : ℝ) ≤ x := by
      have : s ≤ ⌊x⌋₊ := by omega
      exact (Nat.cast_le.2 this).trans (Nat.floor_le hxpos.le)
    have hC0 := mom_C_nonneg s
    have hK0 : 0 ≤ K := by positivity
    by_cases hsY : (s : ℝ) < Y
    · rw [if_pos hsY]
      have hr : (r s : ℝ) ≤ s := by exact_mod_cast mom_r_le s
      have : (r s : ℝ) ^ 2 ≤ Y ^ 2 := by
        apply pow_le_pow_left₀ (by positivity); linarith
      have : 0 ≤ (if Even s ∧ 1 ≤ s then K * C s ^ 2 else 0) := by
        split_ifs <;> positivity
      linarith
    · rw [if_neg hsY, zero_add]
      rw [not_lt] at hsY
      by_cases hev : Even s
      · have hs1 : 1 ≤ s := by
          have : (1 : ℝ) ≤ s := by linarith
          exact_mod_cast this
        rw [if_pos ⟨hev, hs1⟩]
        have hpb := pointwise_bound s hev hsY
        have hspos : (0 : ℝ) < s := by linarith
        set a := Real.log s with ha
        have ha1000 : 1000 ≤ a := by
          have := Real.log_le_log (Real.exp_pos 1000) hsY
          rwa [Real.log_exp] at this
        have hau : a ≤ u := Real.log_le_log hspos hsx
        have hmono := mom_mono a u ha1000 hau
        rw [Real.exp_log hspos, hxu] at hmono
        have hapos : 0 < a := by linarith
        have h1 : (r s : ℝ) ≤ 9 * C s * (x / u ^ 2) := by
          calc (r s : ℝ) ≤ 9 * C s * s / a ^ 2 := hpb
            _ = 9 * C s * (s / a ^ 2) := by ring
            _ ≤ 9 * C s * (x / u ^ 2) := by gcongr
        have h0 : (0 : ℝ) ≤ r s := by positivity
        calc (r s : ℝ) ^ 2 ≤ (9 * C s * (x / u ^ 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
          _ = K * C s ^ 2 := by rw [hK]; field_simp; ring
      · rw [mom_r_odd s hev]
        split_ifs <;> simp; positivity
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite, Finset.sum_const_zero,
    Finset.sum_const_zero, add_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum]
  have hset : (Finset.range (⌊x⌋₊ + 1)).filter (fun s => Even s ∧ 1 ≤ s) =
      (Finset.Icc 1 ⌊x⌋₊).filter Even := by
    ext s; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h3, by omega⟩, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, h3, h1⟩
  rw [hset]
  have hCm := C_mean x hxpos.le
  -- first part: card ≤ Y + 1
  have hcard : (((Finset.range (⌊x⌋₊ + 1)).filter (fun s : ℕ => (s : ℝ) < Y)).card : ℝ)
      ≤ Y + 1 := by
    have : (Finset.range (⌊x⌋₊ + 1)).filter (fun s : ℕ => (s : ℝ) < Y) ⊆
        Finset.range (⌊Y⌋₊ + 1) := by
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢
      have := Nat.le_floor hs.2.le
      omega
    have h := Finset.card_le_card this
    simp only [Finset.card_range] at h
    have h' : ((⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ Y + 1 := by
      push_cast; linarith [Nat.floor_le hYpos.le]
    exact (Nat.cast_le.2 h).trans h'
  -- Y^3 bound: 2 Y^3 * u^4 ≤ 8 x^3
  have hu4 : u ^ 4 ≤ 256 * Real.exp u := by
    have h1 : u / 4 ≤ Real.exp (u / 4) := by
      have := Real.add_one_le_exp (u / 4); linarith
    have h2 : (u / 4) ^ 4 ≤ Real.exp (u / 4) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
    rw [← Real.exp_nat_mul] at h2
    have : ((4 : ℕ) : ℝ) * (u / 4) = u := by push_cast; ring
    rw [this] at h2
    nlinarith
  have hx3 : Real.exp (3 * u) = x ^ 3 := by
    rw [← hxu, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hY3 : 2 * Y ^ 3 * u ^ 4 ≤ 8 * x ^ 3 := by
    have e1 : Y ^ 3 = Real.exp 3000 := by
      rw [hY, ← Real.exp_nat_mul]; norm_num
    have e2 : Real.exp (3 * u) = Real.exp 3000 * Real.exp u * Real.exp (2 * u - 3000) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have e3 : Y ≤ Real.exp (2 * u - 3000) := by
      rw [hY]; apply Real.exp_le_exp.2; linarith
    rw [e1, ← hx3, e2]
    have p1 := Real.exp_pos 3000
    have p2 := Real.exp_pos u
    have : 64 * Real.exp u ≤ Real.exp u * Real.exp (2 * u - 3000) := by nlinarith
    nlinarith
  have hpart1 : (((Finset.range (⌊x⌋₊ + 1)).filter (fun s : ℕ => (s : ℝ) < Y)).card : ℝ)
      * Y ^ 2 ≤ 8 * x ^ 3 / u ^ 4 := by
    rw [le_div_iff₀ (by positivity)]
    have : (Y + 1) * Y ^ 2 ≤ 2 * Y ^ 3 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hcard (sq_nonneg Y)
    have hu0 : 0 ≤ u ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right (h.trans this) hu0]
  have hpart2 : K * ∑ s ∈ (Finset.Icc 1 ⌊x⌋₊).filter Even, C s ^ 2 ≤ 1701 / 2 * x ^ 3 / u ^ 4 := by
    calc K * ∑ s ∈ (Finset.Icc 1 ⌊x⌋₊).filter Even, C s ^ 2 ≤ K * (21 / 2 * x) := by
          gcongr
      _ = 1701 / 2 * x ^ 3 / u ^ 4 := by rw [hK]; ring
  have : 8 * x ^ 3 / u ^ 4 + 1701 / 2 * x ^ 3 / u ^ 4 ≤ 860 * x ^ 3 / u ^ 4 := by
    rw [← add_div]; gcongr; nlinarith [pow_pos hxpos 3]
  linarith

end Schnir

open Schnir in
theorem solution (x : ℝ) (hx : Real.exp 2000 ≤ x) :
    ∑ s ∈ Finset.range (⌊x⌋₊ + 1), (r s : ℝ) ^ 2 ≤ 860 * x ^ 3 / (Real.log x) ^ 4 :=
  Schnir.second_moment x hx
