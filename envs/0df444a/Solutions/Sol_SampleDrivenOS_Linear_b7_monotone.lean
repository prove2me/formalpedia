-- Prove2me | solution 1 for SampleDrivenOS.Linear.b7_monotone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:55:06.470076+00:00
-- url     : https://prove2.me/submissions/0aa9d797-1839-4a9f-80dd-2f648bc3a084

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

lemma S_gterm_bounds {p α : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hα0 : 0 ≤ α) (hα1 : α < 1) (i : ℕ) :
    1 - α ≤ 1 + α * (p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)) - 1) ∧
      1 + α * (p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)) - 1) ≤ 1 := by
  have h1 := S_w_nonneg hp0 hp1 i
  have h2 := S_w_le_one hp0 hp1 i
  constructor <;> nlinarith [mul_nonneg hα0 h1, mul_nonneg hα0 (sub_nonneg.2 h2)]

lemma S_g_summable {p α : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Summable (fun i : ℕ => Real.log (1 + α * (p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)) - 1)) /
      (((i : ℝ) + 1) * ((i : ℝ) + 2))) := by
  refine Summable.of_norm_bounded (S_tele.summable.mul_left (-Real.log (1 - α))) (fun i => ?_)
  obtain ⟨hl, hu⟩ := S_gterm_bounds hp0 hp1 hα0 hα1 i
  have hpos : 0 < 1 + α * (p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)) - 1) := by linarith
  have hlog_le : Real.log (1 + α * (p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)) - 1)) ≤ 0 :=
    Real.log_nonpos hpos.le hu
  have hlog_ge : Real.log (1 - α) ≤ Real.log (1 + α * (p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)) - 1)) :=
    Real.log_le_log (by linarith) hl
  have hA : 0 < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hA, abs_of_nonpos hlog_le]
  rw [show -Real.log (1 - α) * (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) =
    -Real.log (1 - α) / (((i : ℝ) + 1) * ((i : ℝ) + 2)) by ring]
  exact div_le_div_of_nonneg_right (by linarith) hA.le

lemma S_b7 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    StrictMonoOn (fB7 p) (Set.Icc 0 1) ∧ AntitoneOn (gB7 p) (Set.Ico 0 1) := by
  constructor
  · intro a _ b _ hab
    unfold fB7
    have h2 : 0 < (1 - p) ^ 2 := pow_pos (sub_pos.2 hp1) 2
    have : a * (1 - p) ^ 2 / p < b * (1 - p) ^ 2 / p := by
      apply div_lt_div_of_pos_right _ hp0
      nlinarith
    linarith
  · intro a ha b hb hab
    unfold gB7
    refine (S_g_summable hp0 hp1 hb.1 hb.2).tsum_le_tsum (fun i => ?_)
      (S_g_summable hp0 hp1 ha.1 ha.2)
    have hA : 0 < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
    obtain ⟨hl, hu⟩ := S_gterm_bounds hp0 hp1 hb.1 hb.2 i
    have h2 := S_w_le_one hp0 hp1 i
    refine div_le_div_of_nonneg_right (Real.log_le_log (by linarith [hb.2]) ?_) hA.le
    nlinarith [mul_nonneg (sub_nonneg.2 hab) (sub_nonneg.2 h2)]

theorem solution (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    StrictMonoOn (fB7 p) (Set.Icc 0 1) ∧ AntitoneOn (gB7 p) (Set.Ico 0 1) :=
  S_b7 p hp.1 hp.2
