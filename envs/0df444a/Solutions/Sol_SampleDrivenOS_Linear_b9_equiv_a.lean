-- Prove2me | solution 1 for SampleDrivenOS.Linear.b9_equiv_a
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:58:02.74889+00:00
-- url     : https://prove2.me/submissions/41165a71-6698-4ea3-b514-9ea3c6b47e7b

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

theorem solution (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    (Real.log p + s * (1 - p) ^ 2 ≤
      ∑' i : ℕ, Real.log (1 - s * p + s * p * ((i + 2) * p ^ (i + 1) - (i + 1) * p ^ (i + 2))) /
        ((i + 1) * (i + 2))) ↔ s ≤ aB9 s p := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hs0, hs1⟩ := hs
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
  -- the series of logs L_i / A_i is summable
  have hL : Summable (fun i : ℕ =>
      Real.log (1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)))) /
        (((i : ℝ) + 1) * ((i : ℝ) + 2))) := by
    refine Summable.of_norm_bounded
      (S_tele.summable.mul_left (|Real.log (1 / p - s)| + |Real.log (1 / p)|)) (fun i => ?_)
    have hA : 0 < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
    have hlo : Real.log (1 / p - s) ≤
        Real.log (1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)))) :=
      Real.log_le_log hspos (hDge i)
    have hhi : Real.log (1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)))) ≤
        Real.log (1 / p) := Real.log_le_log (hDpos i) (hDle i)
    have hb : |Real.log (1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p))))| ≤
        |Real.log (1 / p - s)| + |Real.log (1 / p)| := by
      rw [abs_le]
      constructor
      · have := neg_abs_le (Real.log (1 / p - s))
        have := abs_nonneg (Real.log (1 / p))
        linarith
      · have := le_abs_self (Real.log (1 / p))
        have := abs_nonneg (Real.log (1 / p - s))
        linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hA,
      show (|Real.log (1 / p - s)| + |Real.log (1 / p)|) * (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) =
        (|Real.log (1 / p - s)| + |Real.log (1 / p)|) / (((i : ℝ) + 1) * ((i : ℝ) + 2)) by ring]
    exact div_le_div_of_nonneg_right hb hA.le
  have hterm : ∀ i : ℕ,
      Real.log (1 - s * p + s * p * (((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2))) /
        (((i : ℝ) + 1) * ((i : ℝ) + 2)) =
      Real.log p * (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) +
        Real.log (1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)))) /
          (((i : ℝ) + 1) * ((i : ℝ) + 2)) := by
    intro i
    have hD := hDpos i
    have e : 1 - s * p + s * p * (((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2)) =
        p * (1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)))) := by
      field_simp
      ring
    rw [e, Real.log_mul hp0.ne' hD.ne']
    ring
  have hsum : ∑' i : ℕ, Real.log (1 - s * p + s * p * (((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2))) /
        (((i : ℝ) + 1) * ((i : ℝ) + 2)) =
      Real.log p + ∑' i : ℕ,
        Real.log (1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)))) /
          (((i : ℝ) + 1) * ((i : ℝ) + 2)) := by
    simp_rw [hterm]
    rw [Summable.tsum_add (S_tele.summable.mul_left _) hL, tsum_mul_left, S_tele.tsum_eq]
    ring
  unfold aB9
  rw [hsum]
  constructor <;> intro h <;> nlinarith
