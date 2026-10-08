-- Prove2me | solution 1 for QueueingFundamentals.AdvMarkov.retrial_steady_state
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T07:13:59.221676+00:00
-- url     : https://prove2.me/submissions/6b78c56a-1e64-43f0-b1b1-d818c1c8bd06

import Mathlib
import Definitions.Def_QueueingFundamentals_AdvMarkov_Retrial

set_option autoImplicit false

namespace RetrialAuxF4B

open Finset QueueingFundamentals.AdvMarkov

lemma prod_eval (b : ℝ) (n : ℕ) : (ascPochhammer ℝ n).eval b = ∏ i ∈ range n, (b + i) := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval, ih, prod_range_succ]

lemma choose_prod (b : ℝ) (n : ℕ) :
    Ring.choose (b + n - 1) n = (∏ i ∈ range n, (b + i)) / n.factorial := by
  rw [← Ring.multichoose_eq]
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer b n
  rw [Polynomial.ascPochhammer_smeval_eq_eval, prod_eval, nsmul_eq_mul] at h
  rw [← h, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]

lemma binom_hasSum (b x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => (∏ i ∈ range n, (b + i)) / n.factorial * x ^ n)
      (1 / (1 - x) ^ b) := by
  have hmem : x ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right]
    simpa [Real.enorm_eq_ofReal_abs, abs_of_nonneg hx0] using hx1
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero b).hasSum hmem
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, zero_add, smul_eq_mul,
    choose_prod] using h

lemma prod_Icc_shift (f : ℕ → ℝ) (n : ℕ) : ∏ i ∈ Icc 1 n, f i = ∏ i ∈ range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, prod_range_succ]

lemma prodA (lam gam : ℝ) (hgam : gam ≠ 0) (n : ℕ) :
    ∏ i ∈ range n, (lam + (i : ℝ) * gam) = gam ^ n * ∏ i ∈ range n, (lam / gam + i) := by
  have : gam ^ n = ∏ _i ∈ range n, gam := by simp
  rw [this, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  field_simp

lemma prodB (lam gam : ℝ) (hgam : gam ≠ 0) (n : ℕ) :
    ∏ i ∈ Icc 1 n, (lam + (i : ℝ) * gam) = gam ^ n * ∏ i ∈ range n, (lam / gam + 1 + i) := by
  rw [prod_Icc_shift (fun i : ℕ => lam + (i : ℝ) * gam)]
  have : gam ^ n = ∏ _i ∈ range n, gam := by simp
  rw [this, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  push_cast
  field_simp
  ring

lemma prod_split (lam gam : ℝ) (n : ℕ) :
    ∏ i ∈ range (n + 1), (lam + (i : ℝ) * gam) = lam * ∏ i ∈ Icc 1 n, (lam + (i : ℝ) * gam) := by
  rw [prod_Icc_shift (fun i : ℕ => lam + (i : ℝ) * gam), prod_range_succ']
  simp [mul_comm]

lemma P0_eq (lam mu gam : ℝ) (hgam : gam ≠ 0) (n : ℕ) :
    retrialP0 lam mu gam n = (1 - lam / mu) ^ (lam / gam + 1) *
      ((∏ i ∈ range n, (lam / gam + i)) / n.factorial * (lam / mu) ^ n) := by
  unfold retrialP0
  rw [prodA lam gam hgam n]
  have : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp

lemma P1_eq (lam mu gam : ℝ) (hgam : gam ≠ 0) (n : ℕ) :
    retrialP1 lam mu gam n = (1 - lam / mu) ^ (lam / gam + 1) * (lam / mu) *
      ((∏ i ∈ range n, (lam / gam + 1 + i)) / n.factorial * (lam / mu) ^ n) := by
  unfold retrialP1
  rw [prodB lam gam hgam n]
  have : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp
  ring

lemma R_h1 (lam mu gam : ℝ) (hmu : mu ≠ 0) (hgam : gam ≠ 0) (n : ℕ) :
    (lam + (n : ℝ) * gam) * retrialP0 lam mu gam n = mu * retrialP1 lam mu gam n := by
  unfold retrialP0 retrialP1
  have hXP := prod_split lam gam n
  rw [prod_range_succ] at hXP
  have : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  calc (lam + (n : ℝ) * gam) * ((1 - lam / mu) ^ (lam / gam + 1) *
        ((lam / mu) ^ n / ((n.factorial : ℝ) * gam ^ n)) * ∏ i ∈ range n, (lam + (i : ℝ) * gam))
      = (1 - lam / mu) ^ (lam / gam + 1) * ((lam / mu) ^ n / ((n.factorial : ℝ) * gam ^ n)) *
          ((∏ i ∈ range n, (lam + (i : ℝ) * gam)) * (lam + (n : ℝ) * gam)) := by ring
    _ = (1 - lam / mu) ^ (lam / gam + 1) * ((lam / mu) ^ n / ((n.factorial : ℝ) * gam ^ n)) *
          (lam * ∏ i ∈ Icc 1 n, (lam + (i : ℝ) * gam)) := by rw [hXP]
    _ = _ := by rw [pow_succ]; field_simp

lemma R_cut (lam mu gam : ℝ) (hmu : mu ≠ 0) (hgam : gam ≠ 0) (n : ℕ) :
    ((n : ℝ) + 1) * gam * retrialP0 lam mu gam (n + 1) = lam * retrialP1 lam mu gam n := by
  unfold retrialP0 retrialP1
  rw [prod_split lam gam n, Nat.factorial_succ]
  have : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  push_cast
  field_simp
  ring

lemma R_balance (lam mu gam : ℝ) (hmu : mu ≠ 0) (hgam : gam ≠ 0) :
    RetrialBalance lam mu gam (retrialP0 lam mu gam) (retrialP1 lam mu gam) := by
  refine ⟨R_h1 lam mu gam hmu hgam, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have e1 := R_h1 lam mu gam hmu hgam (m + 1)
    have e2 := R_cut lam mu gam hmu hgam (m + 1)
    have e3 := R_cut lam mu gam hmu hgam m
    simp only [Nat.add_sub_cancel]
    push_cast at e1 e2 e3 ⊢
    linear_combination -e1 - e2 + e3
  · have e1 := R_h1 lam mu gam hmu hgam 0
    have e3 := R_cut lam mu gam hmu hgam 0
    push_cast at e1 e3
    linear_combination -e1 - e3

lemma cut (lam mu gam : ℝ) (p0 p1 : ℕ → ℝ) (hb : RetrialBalance lam mu gam p0 p1) :
    ∀ n : ℕ, ((n : ℝ) + 1) * gam * p0 (n + 1) = lam * p1 n := by
  obtain ⟨h1, h2, h3⟩ := hb
  intro n
  induction n with
  | zero =>
    have e1 := h1 0
    push_cast at e1 ⊢
    linear_combination -h3 - e1
  | succ n ih =>
    have e1 := h1 (n + 1)
    have e2 := h2 (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at e2
    push_cast at e1 e2 ih ⊢
    linear_combination (-1 : ℝ) * e2 - e1 + ih

lemma recur (lam mu gam : ℝ) (p0 p1 : ℕ → ℝ) (hb : RetrialBalance lam mu gam p0 p1) (n : ℕ) :
    mu * (((n : ℝ) + 1) * gam) * p0 (n + 1) = lam * (lam + (n : ℝ) * gam) * p0 n := by
  have c := cut lam mu gam p0 p1 hb n
  have e1 := hb.1 n
  linear_combination mu * c - lam * e1

end RetrialAuxF4B

open QueueingFundamentals.AdvMarkov in
theorem solution (lam mu gam : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hgam : 0 < gam)
    (hρ1 : lam / mu < 1) :
    IsRetrialSteadyState lam mu gam (retrialP0 lam mu gam) (retrialP1 lam mu gam) ∧
      ∀ p0 p1 : ℕ → ℝ, IsRetrialSteadyState lam mu gam p0 p1 →
        p0 = retrialP0 lam mu gam ∧ p1 = retrialP1 lam mu gam := by
  have hmu0 : mu ≠ 0 := hmu.ne'
  have hgam0 : gam ≠ 0 := hgam.ne'
  have hρ0 : 0 < lam / mu := div_pos hlam hmu
  have hc : 0 < 1 - lam / mu := by linarith
  -- normalization
  have hsum : HasSum (fun n => retrialP0 lam mu gam n + retrialP1 lam mu gam n) 1 := by
    have s0 := (RetrialAuxF4B.binom_hasSum (lam / gam) (lam / mu) hρ0.le hρ1).mul_left
      ((1 - lam / mu) ^ (lam / gam + 1))
    have s1 := (RetrialAuxF4B.binom_hasSum (lam / gam + 1) (lam / mu) hρ0.le hρ1).mul_left
      ((1 - lam / mu) ^ (lam / gam + 1) * (lam / mu))
    have s := s0.add s1
    have hfun : (fun n => retrialP0 lam mu gam n + retrialP1 lam mu gam n) =
        fun n => (1 - lam / mu) ^ (lam / gam + 1) *
          ((∏ i ∈ Finset.range n, (lam / gam + i)) / n.factorial * (lam / mu) ^ n) +
          (1 - lam / mu) ^ (lam / gam + 1) * (lam / mu) *
          ((∏ i ∈ Finset.range n, (lam / gam + 1 + i)) / n.factorial * (lam / mu) ^ n) := by
      funext n
      rw [RetrialAuxF4B.P0_eq lam mu gam hgam0 n, RetrialAuxF4B.P1_eq lam mu gam hgam0 n]
    rw [hfun]
    have hpa : (0 : ℝ) < (1 - lam / mu) ^ (lam / gam) := Real.rpow_pos_of_pos hc _
    have hval : (1 - lam / mu) ^ (lam / gam + 1) * (1 / (1 - lam / mu) ^ (lam / gam)) +
        (1 - lam / mu) ^ (lam / gam + 1) * (lam / mu) * (1 / (1 - lam / mu) ^ (lam / gam + 1))
        = 1 := by
      rw [Real.rpow_add hc, Real.rpow_one]
      have hA0 := hpa.ne'
      generalize (1 - lam / mu) ^ (lam / gam) = A at hA0 ⊢
      have hc0 := hc.ne'
      generalize lam / mu = ρ at hc0 ⊢
      field_simp
      ring
    rw [hval] at s
    exact s
  have hR := RetrialAuxF4B.R_balance lam mu gam hmu0 hgam0
  have hP0nn : ∀ n, 0 ≤ retrialP0 lam mu gam n := fun n =>
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hc.le _) (by positivity))
      (Finset.prod_nonneg fun i _ => by positivity)
  have hP1nn : ∀ n, 0 ≤ retrialP1 lam mu gam n := fun n =>
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hc.le _) (by positivity))
      (Finset.prod_nonneg fun i _ => by positivity)
  refine ⟨⟨hP0nn, hP1nn, hsum, hR⟩, ?_⟩
  rintro p0 p1 ⟨-, -, hps, hpb⟩
  have hR00 : retrialP0 lam mu gam 0 ≠ 0 := by
    unfold retrialP0
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, Finset.range_zero,
      Finset.prod_empty, mul_one, div_one]
    exact (Real.rpow_pos_of_pos hc _).ne'
  set r := p0 0 / retrialP0 lam mu gam 0 with hr
  have h0 : ∀ n, p0 n = r * retrialP0 lam mu gam n := by
    intro n
    induction n with
    | zero => rw [hr]; field_simp
    | succ n ih =>
      have hD : mu * (((n : ℝ) + 1) * gam) ≠ 0 := by positivity
      apply mul_left_cancel₀ hD
      have rp := RetrialAuxF4B.recur lam mu gam p0 p1 hpb n
      have rR := RetrialAuxF4B.recur lam mu gam _ _ hR n
      linear_combination rp + lam * (lam + (n : ℝ) * gam) * ih - r * rR
  have h1 : ∀ n, p1 n = r * retrialP1 lam mu gam n := by
    intro n
    apply mul_left_cancel₀ hmu0
    have e1 := hpb.1 n
    have e2 := hR.1 n
    linear_combination -e1 + (lam + (n : ℝ) * gam) * h0 n + r * e2
  have hfun : (fun n => p0 n + p1 n) =
      fun n => r * (retrialP0 lam mu gam n + retrialP1 lam mu gam n) := by
    funext n; rw [h0 n, h1 n]; ring
  rw [hfun] at hps
  have hr1 : r * 1 = 1 := (hsum.mul_left r).unique hps
  rw [mul_one] at hr1
  refine ⟨funext fun n => ?_, funext fun n => ?_⟩
  · rw [h0 n, hr1, one_mul]
  · rw [h1 n, hr1, one_mul]
