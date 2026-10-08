-- Prove2me | solution 1 for PoissonDepTrials.SecondOrder.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:12:48.07678+00:00
-- url     : https://prove2.me/submissions/0dec63a3-7f31-44a4-a5df-b4e86532e5cb

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

open PoissonDepTrials.SecondOrder in
theorem solution (lam b : ℝ) (hb : 0 < b) (hbl : b ≤ lam) (k : ℕ) :
    |Real.exp (-lam) * lam ^ k - Real.exp (-b) * b ^ k| ≤
      (lam - b) * (Real.exp (-lam) * k * lam ^ (k - 1) + Real.exp (-b) * b ^ k) := by
  have hl : 0 < lam := lt_of_lt_of_le hb hbl
  have hd : 0 ≤ lam - b := sub_nonneg.mpr hbl
  -- A := e^{-lam} (lam^k - b^k) ∈ [0, e^{-lam} (lam-b) k lam^(k-1)]
  have hpow : |lam ^ k - b ^ k| ≤ |lam - b| * k * max |lam| |b| ^ (k - 1) :=
    abs_pow_sub_pow_le lam b k
  rw [abs_of_nonneg hd, abs_of_pos hl, abs_of_pos hb, max_eq_left hbl] at hpow
  have hA0 : 0 ≤ lam ^ k - b ^ k :=
    sub_nonneg.mpr (pow_le_pow_left₀ hb.le hbl k)
  rw [abs_of_nonneg hA0] at hpow
  -- B := b^k (e^{-lam} - e^{-b}) ∈ [-(lam-b) e^{-b} b^k, 0]
  have he1 : Real.exp (-lam) ≤ Real.exp (-b) := Real.exp_le_exp.mpr (by linarith)
  have he2 : Real.exp (-b) - Real.exp (-lam) ≤ (lam - b) * Real.exp (-b) := by
    have h1 : 1 - (lam - b) ≤ Real.exp (-(lam - b)) := by
      have := Real.add_one_le_exp (-(lam - b)); linarith
    have h2 : Real.exp (-lam) = Real.exp (-b) * Real.exp (-(lam - b)) := by
      rw [← Real.exp_add]; ring_nf
    rw [h2]
    have hpos := Real.exp_pos (-b)
    nlinarith
  have hbk : 0 ≤ b ^ k := pow_nonneg hb.le k
  have hel := Real.exp_pos (-lam)
  have key : Real.exp (-lam) * lam ^ k - Real.exp (-b) * b ^ k
      = Real.exp (-lam) * (lam ^ k - b ^ k) + b ^ k * (Real.exp (-lam) - Real.exp (-b)) := by
    ring
  rw [key, abs_le]
  have hA1 : Real.exp (-lam) * (lam ^ k - b ^ k) ≤ Real.exp (-lam) * ((lam - b) * k * lam ^ (k - 1)) :=
    mul_le_mul_of_nonneg_left hpow hel.le
  have hA2 : 0 ≤ Real.exp (-lam) * (lam ^ k - b ^ k) := mul_nonneg hel.le hA0
  have hB1 : b ^ k * (Real.exp (-lam) - Real.exp (-b)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hbk (by linarith)
  have hB2 : b ^ k * (Real.exp (-b) - Real.exp (-lam)) ≤ b ^ k * ((lam - b) * Real.exp (-b)) :=
    mul_le_mul_of_nonneg_left he2 hbk
  have hC : 0 ≤ (lam - b) * (Real.exp (-lam) * k * lam ^ (k - 1)) :=
    mul_nonneg hd (by positivity)
  have hD : 0 ≤ (lam - b) * (Real.exp (-b) * b ^ k) := mul_nonneg hd (by positivity)
  constructor <;> nlinarith
