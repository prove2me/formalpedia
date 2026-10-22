-- Prove2me | solution 1 for SampleDrivenOS.Linear.b9_b_ge
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:47:47.096754+00:00
-- url     : https://prove2.me/submissions/cafedec9-79cf-43d9-bbba-f3cb9579ee87

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting

set_option autoImplicit false
open SampleDrivenOS.Linear

lemma S_tele : HasSum (fun i : ℕ => 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) 1 := by
  have h : ∀ n : ℕ, ∑ i ∈ Finset.range n, 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)) = 1 - 1 / ((n : ℝ) + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp
      ring
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => by positivity)]
  simp_rw [h]
  have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this

lemma S_w_nonneg {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : ℕ) :
    0 ≤ p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)) := by
  have : 0 ≤ 1 - p := by linarith
  positivity

lemma S_w_le_one_aux {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (k : ℕ) :
    p ^ k * (1 + (k : ℝ) * (1 - p)) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : p ^ k * (1 + (k : ℝ) * (1 - p)) - p ^ (k + 1) * (1 + ((k + 1 : ℕ) : ℝ) * (1 - p))
        = p ^ k * (1 - p) ^ 2 * ((k : ℝ) + 1) := by push_cast; ring
    have : 0 ≤ p ^ k * (1 - p) ^ 2 * ((k : ℝ) + 1) := by positivity
    linarith

lemma S_w_le_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : ℕ) :
    p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)) ≤ 1 := by
  have := S_w_le_one_aux hp0 hp1 (i + 1)
  push_cast at this
  exact this

theorem solution (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    1 / p ≤ bB9 s p := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hp0, hp1⟩ := hp
  have hspos : 0 < 1 / p - s := by
    have : 1 < 1 / p := (one_lt_one_div hp0 hp1)
    linarith
  have hDge : ∀ i : ℕ, 1 / p - s ≤ 1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p))) := by
    intro i
    have h1 := S_w_nonneg hp0 hp1 i
    nlinarith
  have hDle : ∀ i : ℕ, 1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p))) ≤ 1 / p := by
    intro i
    have h1 := S_w_le_one hp0 hp1 i
    nlinarith
  have hDpos : ∀ i : ℕ, 0 < 1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p))) :=
    fun i => lt_of_lt_of_le hspos (hDge i)
  have hS0 : HasSum (fun i : ℕ => p * (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)))) p := by
    simpa using S_tele.mul_left p
  have hSsum : Summable (fun i : ℕ => 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2) *
      (1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)))))) := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
      (S_tele.summable.mul_left (1 / (1 / p - s)))
    · have := hDpos i
      positivity
    · have h1 := hDpos i
      have h2 := hDge i
      have hA : 0 < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
      rw [show 1 / (1 / p - s) * (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) =
        1 / (((i : ℝ) + 1) * ((i : ℝ) + 2) * (1 / p - s)) by field_simp]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hterm : ∀ i : ℕ, p * (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) ≤ 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2) *
      (1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p))))) := by
    intro i
    have h1 := hDpos i
    have h2 := hDle i
    have hA : 0 < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
    rw [show p * (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) = 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2) * (1 / p)) by
      field_simp]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have key : p ≤ ∑' i : ℕ, 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2) *
      (1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p))))) := by
    calc p = ∑' i : ℕ, p * (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) := hS0.tsum_eq.symm
      _ ≤ _ := hS0.summable.tsum_le_tsum hterm hSsum
  unfold bB9
  calc 1 / p = 1 / p ^ 2 * p := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left key (by positivity)
