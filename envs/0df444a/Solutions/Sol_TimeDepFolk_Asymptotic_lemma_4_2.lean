-- Prove2me | solution 1 for TimeDepFolk.Asymptotic.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:11:59.369434+00:00
-- url     : https://prove2.me/submissions/895e7dfa-5282-4e62-9671-82a17251c342

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model

namespace TDFTail

open TimeDepFolk.Asymptotic Finset

theorem summable_shift (θ : Evaluation) (n : ℕ) : Summable (fun r => θ.θ (n + r)) := by
  have := (summable_nat_add_iff n).2 θ.hasSum.summable
  simpa [add_comm] using this

theorem tail_nonneg (θ : Evaluation) (n : ℕ) : 0 ≤ ∑' r, θ.θ (n + r) :=
  tsum_nonneg fun r => θ.nonneg _

theorem cont_nonneg (θ : Evaluation) (n t : ℕ) : 0 ≤ cont θ.θ n t :=
  div_nonneg (θ.nonneg _) (tail_nonneg θ n)

theorem cont_le_zero (θ : Evaluation) (n t : ℕ) : cont θ.θ n t ≤ cont θ.θ n 0 :=
  div_le_div_of_nonneg_right (θ.antitone (by omega)) (tail_nonneg θ n)

theorem cont_antitone (θ : Evaluation) (n : ℕ) : Antitone (cont θ.θ n) :=
  fun _ _ h => div_le_div_of_nonneg_right (θ.antitone (by omega)) (tail_nonneg θ n)

theorem hasSum_cont (θ : Evaluation) (n : ℕ) (h : 0 < ∑' r, θ.θ (n + r)) :
    HasSum (cont θ.θ n) 1 := by
  have := ((summable_shift θ n).hasSum).div_const (∑' r, θ.θ (n + r))
  rwa [div_self h.ne'] at this

theorem sum_range_cont (θ : Evaluation) (n m : ℕ) :
    ∑ t ∈ range m, cont θ.θ n t = (∑ t ∈ range m, θ.θ (n + t)) / ∑' r, θ.θ (n + r) := by
  simp only [cont, Finset.sum_div]

theorem tail_split (θ : Evaluation) (n m : ℕ) :
    ∑' r, θ.θ (n + r) = ∑ r ∈ range m, θ.θ (n + r) + ∑' r, θ.θ (n + m + r) := by
  have := (summable_shift θ n).sum_add_tsum_nat_add m
  rw [← this]
  congr 1
  refine tsum_congr fun r => ?_
  congr 1; omega

end TDFTail

namespace TDF42

open TimeDepFolk.Asymptotic Finset

/-- If all consecutive ratios are below `1 + ε` (`ε < 1`), all weights are positive and
consecutive ratios are well defined. -/
theorem pos_of_ratio (θ : Evaluation) (ε : ℝ) (hε1 : ε < 1)
    (h : ∀ t, dist (1 : ℝ) (θ.θ t / θ.θ (t + 1)) < ε) : ∀ t, 0 < θ.θ (t + 1) := by
  intro t
  rcases (θ.nonneg (t + 1)).eq_or_lt with h0 | h0
  · have := h t
    rw [← h0, div_zero, dist_zero_right, norm_one] at this
    linarith
  · exact h0

theorem ratio_lt (θ : Evaluation) (ε : ℝ) (h : ∀ t, dist (1 : ℝ) (θ.θ t / θ.θ (t + 1)) < ε)
    (t : ℕ) : θ.θ t / θ.θ (t + 1) < 1 + ε := by
  have := h t
  rw [Real.dist_eq] at this
  have := (abs_lt.1 this).1
  linarith

theorem geom_lower (θ : Evaluation) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (h : ∀ t, dist (1 : ℝ) (θ.θ t / θ.θ (t + 1)) < ε) (n : ℕ) :
    ∀ r, θ.θ n * (1 / (1 + ε)) ^ r ≤ θ.θ (n + r) := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
    have hp := pos_of_ratio θ ε hε1 h (n + r)
    have hr := ratio_lt θ ε h (n + r)
    rw [div_lt_iff₀ hp] at hr
    rw [pow_succ, ← mul_assoc, ← add_assoc]
    calc θ.θ n * (1 / (1 + ε)) ^ r * (1 / (1 + ε)) ≤ θ.θ (n + r) * (1 / (1 + ε)) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
      _ ≤ θ.θ (n + r + 1) := by
          rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith

theorem cont_zero_le (θ : Evaluation) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (h : ∀ t, dist (1 : ℝ) (θ.θ t / θ.θ (t + 1)) < ε) (n : ℕ) :
    cont θ.θ n 0 ≤ ε / (1 + ε) := by
  set q := 1 / (1 + ε) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one (by linarith)]; linarith
  have hθn : 0 < θ.θ n := by
    rcases n with _ | n
    · exact lt_of_lt_of_le (pos_of_ratio θ ε hε1 h 0) (θ.antitone (Nat.zero_le 1))
    · exact pos_of_ratio θ ε hε1 h n
  have hsum : θ.θ n * (1 - q)⁻¹ ≤ ∑' r, θ.θ (n + r) := by
    rw [← tsum_geometric_of_lt_one hq0 hq1, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (geom_lower θ ε hε hε1 h n)
      ((summable_geometric_of_lt_one hq0 hq1).mul_left _) (TDFTail.summable_shift θ n)
  have h1q : 1 - q = ε / (1 + ε) := by rw [hq]; field_simp; ring
  have hpos : 0 < θ.θ n * (1 - q)⁻¹ := by
    have : 0 < 1 - q := by linarith
    positivity
  unfold cont
  simp only [add_zero]
  calc θ.θ n / ∑' r, θ.θ (n + r) ≤ θ.θ n / (θ.θ n * (1 - q)⁻¹) :=
        div_le_div_of_nonneg_left hθn.le hpos hsum
    _ = ε / (1 + ε) := by rw [div_mul_eq_div_div, div_self hθn.ne', one_div, inv_inv, h1q]

end TDF42

open TimeDepFolk.Asymptotic

theorem solution (θ : ℕ → Evaluation) (hθ : IsPatient θ) :
    TendstoUniformly (fun k n => cont (θ k).θ n 0) (fun _ => (0 : ℝ)) Filter.atTop ∧
      TendstoUniformly
        (fun k (p : ℕ × ℕ) => cont (θ k).θ p.1 p.2 / cont (θ k).θ p.1 (p.2 + 1))
        (fun _ => (1 : ℝ)) Filter.atTop := by
  rw [IsPatient, Metric.tendstoUniformly_iff] at hθ
  constructor
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    set ε' := min (ε / 2) (1 / 2) with hε'
    have hε'0 : 0 < ε' := by positivity
    have hε'1 : ε' < 1 := by
      have := min_le_right (ε / 2) (1 / 2); linarith
    filter_upwards [hθ ε' hε'0] with k hk n
    have h1 := TDF42.cont_zero_le (θ k) ε' hε'0 hε'1 hk n
    have h2 := TDFTail.cont_nonneg (θ k) n 0
    rw [dist_zero_left, Real.norm_eq_abs, abs_of_nonneg h2]
    have h3 : ε' / (1 + ε') ≤ ε' := div_le_self hε'0.le (by linarith)
    have h4 : ε' ≤ ε / 2 := min_le_left _ _
    linarith
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    set ε' := min ε (1 / 2) with hε'
    have hε'0 : 0 < ε' := by positivity
    have hε'1 : ε' < 1 := by
      have := min_le_right ε (1 / 2); linarith
    filter_upwards [hθ ε' hε'0] with k hk p
    have hpos : 0 < ∑' r, (θ k).θ (p.1 + r) := by
      refine lt_of_lt_of_le (TDF42.pos_of_ratio (θ k) ε' hε'1 hk p.1) ?_
      have := (TDFTail.summable_shift (θ k) p.1).le_tsum 1 (fun r _ => (θ k).nonneg _)
      simpa using this
    have e : cont (θ k).θ p.1 p.2 / cont (θ k).θ p.1 (p.2 + 1) =
        (θ k).θ (p.1 + p.2) / (θ k).θ (p.1 + p.2 + 1) := by
      unfold cont
      rw [div_div_div_cancel_right₀ hpos.ne', add_assoc]
    rw [e]
    exact lt_of_lt_of_le (hk (p.1 + p.2)) (min_le_left _ _)
