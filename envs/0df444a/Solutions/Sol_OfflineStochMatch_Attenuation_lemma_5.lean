-- Prove2me | solution 1 for OfflineStochMatch.Attenuation.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T07:24:41.009909+00:00
-- url     : https://prove2.me/submissions/bbbcc2c8-a7b7-4084-b770-a39750610536

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting

namespace OfflineStochMatch.Attenuation.Lemma5Aux

open Real

/-- Product-of-sums identity for coin weights: `∑_b ∏_i bern(q i)(b i) g_i(b i) = ∏_i (…)`. -/
lemma sum_coinWeight_mul_prod (k : ℕ) (q : Fin k → ℝ) (g : Bool → ℝ) :
    ∑ b : Fin k → Bool, coinWeight q b * ∏ i, g (b i)
      = ∏ i, (q i * g true + (1 - q i) * g false) := by
  unfold coinWeight
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (c : Bool) => bern (q i) c * g c)]
  apply Finset.prod_congr rfl
  intro i _
  simp [bern]

lemma coinWeight_nonneg (k : ℕ) (q : Fin k → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (b : Fin k → Bool) : 0 ≤ coinWeight q b := by
  unfold coinWeight
  apply Finset.prod_nonneg
  intro i _
  unfold bern
  split_ifs
  · exact (hq i).1
  · linarith [(hq i).2]

end OfflineStochMatch.Attenuation.Lemma5Aux

open OfflineStochMatch.Attenuation OfflineStochMatch.Attenuation.Lemma5Aux in
theorem solution (k : ℕ) (q : Fin k → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    1 - Real.exp (-(ε ^ 2 / (2 + ε) * ∑ j, q j))
      ≤ ∑ b : Fin k → Bool,
          coinWeight q b *
            (if (((Finset.univ.filter (fun i => b i = true)).card : ℕ) : ℝ) < (1 + ε) * ∑ j, q j
              then 1 else 0) := by
  set μ := ∑ j, q j with hμ
  have hμ0 : 0 ≤ μ := Finset.sum_nonneg (fun i _ => (hq i).1)
  set S : (Fin k → Bool) → ℝ :=
    fun b => (((Finset.univ.filter (fun i => b i = true)).card : ℕ) : ℝ) with hS
  set L := Real.log (1 + ε) with hL
  have hL0 : 0 < L := Real.log_pos (by linarith)
  -- total mass one
  have hsum1 : ∑ b : Fin k → Bool, coinWeight q b = 1 := by
    have := sum_coinWeight_mul_prod k q (fun _ => 1)
    simp only [Finset.prod_const_one, mul_one] at this
    rw [this]
    apply Finset.prod_eq_one
    intro i _; ring
  -- exp(L * S b) as a product
  have hSprod : ∀ b : Fin k → Bool,
      Real.exp (L * S b) = ∏ i, (fun c : Bool => if c then 1 + ε else 1) (b i) := by
    intro b
    have hc : S b = ∑ i, (if b i = true then (1 : ℝ) else 0) := by
      simp only [hS]
      rw [Finset.card_filter]
      push_cast
      rfl
    rw [hc, Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    by_cases h : b i = true
    · simp [h, hL, Real.exp_log (by linarith : (0:ℝ) < 1 + ε)]
    · simp [h]
  -- MGF bound
  have hmgf : ∑ b : Fin k → Bool, coinWeight q b * Real.exp (L * S b) ≤ Real.exp (ε * μ) := by
    simp_rw [hSprod]
    rw [sum_coinWeight_mul_prod k q (fun c : Bool => if c then 1 + ε else 1)]
    simp only [if_true, Bool.false_eq_true, if_false, mul_one]
    rw [hμ, Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro i _; nlinarith [(hq i).1, (hq i).2]
    · intro i _
      have := Real.add_one_le_exp (ε * q i)
      linarith
  -- Markov
  have hmarkov : ∀ b : Fin k → Bool,
      (if S b < (1 + ε) * μ then (0 : ℝ) else 1)
        ≤ Real.exp (L * S b) * Real.exp (-(L * ((1 + ε) * μ))) := by
    intro b
    split_ifs with h
    · positivity
    · rw [← Real.exp_add]
      apply Real.one_le_exp
      push_neg at h
      nlinarith
  have htail : ∑ b : Fin k → Bool, coinWeight q b * (if S b < (1 + ε) * μ then (0 : ℝ) else 1)
      ≤ Real.exp (ε * μ) * Real.exp (-(L * ((1 + ε) * μ))) := by
    calc _ ≤ ∑ b : Fin k → Bool, coinWeight q b *
            (Real.exp (L * S b) * Real.exp (-(L * ((1 + ε) * μ)))) := by
          apply Finset.sum_le_sum
          intro b _
          exact mul_le_mul_of_nonneg_left (hmarkov b) (coinWeight_nonneg k q hq b)
      _ = (∑ b : Fin k → Bool, coinWeight q b * Real.exp (L * S b)) *
            Real.exp (-(L * ((1 + ε) * μ))) := by
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro b _; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hmgf (Real.exp_pos _).le
  -- the analytic inequality  ε - (1+ε) log(1+ε) ≤ -ε²/(2+ε)
  have hlog : 2 * ε / (ε + 2) ≤ L := Real.le_log_one_add_of_nonneg hε.le
  have hexpo : ε * μ + -(L * ((1 + ε) * μ)) ≤ -(ε ^ 2 / (2 + ε) * μ) := by
    have h2 : 0 < ε + 2 := by linarith
    have key : ε - (1 + ε) * L ≤ -(ε ^ 2 / (2 + ε)) := by
      have : (1 + ε) * (2 * ε / (ε + 2)) = ε + ε ^ 2 / (2 + ε) := by
        field_simp; ring
      nlinarith [mul_le_mul_of_nonneg_left hlog (by linarith : (0:ℝ) ≤ 1 + ε)]
    nlinarith [mul_le_mul_of_nonneg_right key hμ0]
  have htail' : ∑ b : Fin k → Bool, coinWeight q b * (if S b < (1 + ε) * μ then (0 : ℝ) else 1)
      ≤ Real.exp (-(ε ^ 2 / (2 + ε) * μ)) := by
    refine le_trans htail ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hexpo
  have hsplit : ∑ b : Fin k → Bool, coinWeight q b * (if S b < (1 + ε) * μ then (1 : ℝ) else 0)
      = 1 - ∑ b : Fin k → Bool, coinWeight q b * (if S b < (1 + ε) * μ then (0 : ℝ) else 1) := by
    have hab : ∑ b : Fin k → Bool, coinWeight q b * (if S b < (1 + ε) * μ then (1 : ℝ) else 0)
        + ∑ b : Fin k → Bool, coinWeight q b * (if S b < (1 + ε) * μ then (0 : ℝ) else 1) = 1 := by
      rw [← Finset.sum_add_distrib]
      refine (Finset.sum_congr rfl ?_).trans hsum1
      intro b _
      split_ifs <;> ring
    linarith
  change 1 - Real.exp (-(ε ^ 2 / (2 + ε) * μ)) ≤
    ∑ b : Fin k → Bool, coinWeight q b * (if S b < (1 + ε) * μ then (1 : ℝ) else 0)
  rw [hsplit]
  linarith
