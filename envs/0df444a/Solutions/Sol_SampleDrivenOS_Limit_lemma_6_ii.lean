-- Prove2me | solution 1 for SampleDrivenOS.Limit.lemma_6_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T17:54:44.607434+00:00
-- url     : https://prove2.me/submissions/5c928052-41a6-4909-8bc8-91f4d89c0e35

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting

open MeasureTheory Filter Topology

namespace Lemma6iiAux

open SampleDrivenOS.Limit

/-- `c_{j+1} = (j+1)p^j - j p^{j+1} ∈ [0,1]` -/
lemma c_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (j : ℕ) :
    0 ≤ ((j : ℝ) + 1) * p ^ j - (j : ℝ) * p ^ (j + 1) := by
  have h : ((j : ℝ) + 1) * p ^ j - (j : ℝ) * p ^ (j + 1) = p ^ j * (((j : ℝ) + 1) - (j : ℝ) * p) := by
    ring
  rw [h]
  apply mul_nonneg (pow_nonneg hp0 _)
  have : (j : ℝ) * p ≤ (j : ℝ) := by
    have : (0:ℝ) ≤ (j : ℝ) := by positivity
    nlinarith
  linarith

lemma c_le_one (p : ℝ) (hp0 : 0 ≤ p) (j : ℕ) :
    ((j : ℝ) + 1) * p ^ j - (j : ℝ) * p ^ (j + 1) ≤ 1 := by
  induction j with
  | zero => simp
  | succ n ih =>
    have key : (((n + 1 : ℕ) : ℝ) + 1) * p ^ (n + 1) - ((n + 1 : ℕ) : ℝ) * p ^ (n + 1 + 1)
        = (((n : ℝ) + 1) * p ^ n - (n : ℝ) * p ^ (n + 1)) - ((n : ℝ) + 1) * p ^ n * (1 - p) ^ 2 := by
      push_cast; ring
    rw [key]
    have : 0 ≤ ((n : ℝ) + 1) * p ^ n * (1 - p) ^ 2 := by positivity
    linarith

lemma gamma_eq (p α : ℝ) (j : ℕ) :
    gammaK p α (j + 1) = 1 - α + α * (((j : ℝ) + 1) * p ^ j - (j : ℝ) * p ^ (j + 1)) := by
  simp only [gammaK]
  have : j + 1 - 1 = j := by omega
  rw [this]; push_cast; ring

lemma gamma_bounds (p α : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hα0 : 0 ≤ α) (j : ℕ) :
    1 - α ≤ gammaK p α (j + 1) ∧ gammaK p α (j + 1) ≤ 1 := by
  rw [gamma_eq]
  have h0 := c_nonneg p hp0 hp1 j
  have h1 := c_le_one p hp0 j
  constructor <;> nlinarith

lemma gamma_one (p α : ℝ) : gammaK p α 1 = 1 := by
  simp [gammaK]

lemma tSeq_pos (p α : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hα : α ∈ Set.Ioo (0:ℝ) 1) :
    ∀ n, 0 < tSeq p α n := by
  have hg : ∀ j : ℕ, 0 < gammaK p α (j + 1) := by
    intro j
    have := (gamma_bounds p α hp0.le hp1.le hα.1.le j).1
    linarith [hα.2]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [tSeq, hp0]
    | 1 => simp [tSeq, hp0]
    | 2 => simp only [tSeq]; positivity
    | (k + 3) =>
      rw [tSeq]
      apply mul_pos (ih (k + 2) (by omega))
      apply Real.rpow_pos_of_pos
      exact div_pos (hg k) (hg (k + 1))

/-- closed form of `log t_{n+3}` -/
lemma log_tSeq (p α : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hα : α ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) :
    Real.log (tSeq p α (n + 3)) = (Real.log p + α * (1 - p) ^ 2 / p)
      - ∑ i ∈ Finset.range n, Real.log (gammaK p α (i + 2)) / (((i : ℝ) + 1) * ((i : ℝ) + 2))
      - Real.log (gammaK p α (n + 2)) / ((n : ℝ) + 1) := by
  have hg : ∀ j : ℕ, 0 < gammaK p α (j + 1) := by
    intro j
    have := (gamma_bounds p α hp0.le hp1.le hα.1.le j).1
    linarith [hα.2]
  have hpos := tSeq_pos p α hp0 hp1 hα
  have hstep : ∀ k : ℕ, Real.log (tSeq p α (k + 3)) = Real.log (tSeq p α (k + 2)) +
      (Real.log (gammaK p α (k + 1)) - Real.log (gammaK p α (k + 2))) / ((k : ℝ) + 1) := by
    intro k
    rw [tSeq, Real.log_mul (hpos _).ne' (Real.rpow_pos_of_pos (div_pos (hg k) (hg (k + 1))) _).ne',
      Real.log_rpow (div_pos (hg k) (hg (k + 1))), Real.log_div (hg k).ne' (hg (k + 1)).ne']
    ring
  have h2 : Real.log (tSeq p α 2) = Real.log p + α * (1 - p) ^ 2 / p := by
    simp only [tSeq]
    rw [Real.log_mul hp0.ne' (Real.exp_pos _).ne', Real.log_exp]
  induction n with
  | zero =>
    rw [hstep, h2, gamma_one, Real.log_one]
    simp only [Finset.range_zero, Finset.sum_empty, CharP.cast_eq_zero, zero_add, div_one]
    ring
  | succ n ih =>
    rw [hstep, ih, Finset.sum_range_succ]
    push_cast
    field_simp
    ring

end Lemma6iiAux

open Lemma6iiAux SampleDrivenOS.Limit in
theorem solution (p α : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) (hα : α ∈ Set.Ioo (0:ℝ) 1) :
    ∃ L : ℝ, Tendsto (fun k => SampleDrivenOS.Limit.tSeq p α k) atTop (𝓝 L) ∧
      (L ≤ 1 ↔ Real.log p + α * (1 - p) ^ 2 / p ≤
          ∑' i : ℕ, Real.log (SampleDrivenOS.Limit.gammaK p α (i + 2)) /
            (((i : ℝ) + 1) * ((i : ℝ) + 2))) ∧
      (Real.log p + α * (1 - p) ^ 2 / p =
          ∑' i : ℕ, Real.log (SampleDrivenOS.Limit.gammaK p α (i + 2)) /
            (((i : ℝ) + 1) * ((i : ℝ) + 2)) →
        L = 1) := by
  obtain ⟨hp0, hp1⟩ := hp
  set C := Real.log p + α * (1 - p) ^ 2 / p
  set a : ℕ → ℝ := fun i => Real.log (gammaK p α (i + 2)) / (((i : ℝ) + 1) * ((i : ℝ) + 2))
  set S := ∑' i : ℕ, a i
  have hgb : ∀ j : ℕ, |Real.log (gammaK p α (j + 1))| ≤ -Real.log (1 - α) := by
    intro j
    obtain ⟨hlo, hhi⟩ := gamma_bounds p α hp0.le hp1.le hα.1.le j
    have h1 : 0 < 1 - α := by linarith [hα.2]
    have hpos : 0 < gammaK p α (j + 1) := by linarith
    rw [abs_of_nonpos (Real.log_nonpos hpos.le hhi)]
    have := Real.log_le_log h1 hlo
    linarith
  -- summability
  have hsum : Summable a := by
    have h2 : Summable (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) := by
      have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
      simpa using this
    refine Summable.of_norm_bounded (g := fun i : ℕ => (-Real.log (1 - α)) * (1 / ((i : ℝ) + 1) ^ 2))
      (h2.mul_left _) (fun i => ?_)
    have hd : 0 < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
    simp only [a, Real.norm_eq_abs, abs_div, abs_of_pos hd, div_eq_mul_one_div (|_|)]
    apply mul_le_mul (hgb (i + 1)) _ (by positivity) (le_trans (abs_nonneg _) (hgb 0))
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  -- the boundary term tends to 0
  have hbd : Tendsto (fun n : ℕ => Real.log (gammaK p α (n + 2)) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have : Tendsto (fun n : ℕ => Real.log (gammaK p α (n + 2)) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      apply squeeze_zero_norm (a := fun n : ℕ => (-Real.log (1 - α)) * (1 / ((n : ℝ) + 1)))
      · intro n
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / ((n : ℝ) + 1))]
        exact mul_le_mul_of_nonneg_right (hgb (n + 1)) (by positivity)
      · simpa using hinv.const_mul (-Real.log (1 - α))
    refine this.congr (fun n => ?_)
    ring
  have hlog : Tendsto (fun n : ℕ => Real.log (tSeq p α (n + 3))) atTop (𝓝 (C - S)) := by
    have hfun : (fun n : ℕ => Real.log (tSeq p α (n + 3))) =
        fun n => C - ∑ i ∈ Finset.range n, a i - Real.log (gammaK p α (n + 2)) / ((n : ℝ) + 1) := by
      funext n; exact log_tSeq p α hp0 hp1 hα n
    rw [hfun]
    have := ((tendsto_const_nhds (x := C)).sub hsum.hasSum.tendsto_sum_nat).sub hbd
    rw [sub_zero] at this
    exact this
  have hpos := tSeq_pos p α hp0 hp1 ⟨hα.1, hα.2⟩
  have hT3 : Tendsto (fun n : ℕ => tSeq p α (n + 3)) atTop (𝓝 (Real.exp (C - S))) := by
    have := (Real.continuous_exp.tendsto _).comp hlog
    refine this.congr (fun n => ?_)
    simp only [Function.comp]
    rw [Real.exp_log (hpos _)]
  refine ⟨Real.exp (C - S), (tendsto_add_atTop_iff_nat 3).1 hT3, ?_, ?_⟩
  · rw [Real.exp_le_one_iff, sub_nonpos]
  · intro h
    have : C - S = 0 := by rw [sub_eq_zero]; exact h
    rw [this, Real.exp_zero]
