-- Prove2me | solution 1 for TimeDepFolk.Asymptotic.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:10:18.137611+00:00
-- url     : https://prove2.me/submissions/b2935955-6977-472c-a6c8-275dfff5590c

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

open TimeDepFolk.Asymptotic Finset

theorem solution {I : Type*} {A : I → Type*} (g : I → (∀ i, A i) → ℝ)
    (M : ℝ) (hM : 0 < M) (hgM : ∀ i a, |g i a| ≤ M)
    (ε κ η : ℝ) (hε : 0 < ε) (hκ : 0 < κ) (hη : 0 < η)
    (hη1 : η < ε / (8 * M + 1)) (hη2 : η < 1 / (2 * M)) (hη3 : η < κ / 8)
    (hη4 : η < κ * ε / (48 * M + 16 * ε + 4 * κ))
    (θ : Evaluation) (n L : ℕ) (hL : IsPunLength θ κ η n L)
    (a : Fin L → ∀ i, A i) (j : I) :
    |zvec g (cont θ.θ n) a j| ≤ ε / 2 := by
  set w := cont θ.θ n with hw
  set W := ∑ t ∈ range L, w t with hW
  have hw0 : ∀ t, 0 ≤ w t := TDFTail.cont_nonneg θ n
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun t _ => hw0 t
  have hWlt : W < 4 * η / κ := by
    have h := hL.2.2
    rw [Finset.sum_range_succ] at h
    linarith [hw0 L]
  have h4 : 4 * η / κ ≤ 1 / 2 := by
    rw [div_le_iff₀ hκ]; linarith
  -- the weighted average payoff is bounded by `M`
  have havg : |avgPay g w a j| ≤ M := by
    unfold avgPay
    rw [abs_div, abs_of_nonneg hW0]
    rcases hW0.eq_or_lt with h0 | hpos
    · rw [← h0, div_zero]; exact hM.le
    rw [div_le_iff₀ hpos]
    calc |∑ t : Fin L, w t * g j (a t)| ≤ ∑ t : Fin L, |w t * g j (a t)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t : Fin L, w t * M := by
          refine Finset.sum_le_sum fun t _ => ?_
          rw [abs_mul, abs_of_nonneg (hw0 t)]
          exact mul_le_mul_of_nonneg_left (hgM _ _) (hw0 t)
      _ = M * W := by
          rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun t => w t), mul_comm]
  -- the diamond factor is at most `2W`
  have hdia : 0 ≤ diamond w L ∧ diamond w L ≤ 2 * W := by
    unfold diamond
    rw [← hW]
    have h1 : 0 < 1 - W := by linarith
    refine ⟨div_nonneg hW0 h1.le, ?_⟩
    rw [div_le_iff₀ h1]; nlinarith
  unfold zvec
  rw [abs_mul, abs_of_nonneg hdia.1]
  have hden : 16 * M ≤ 48 * M + 16 * ε + 4 * κ := by linarith
  have hη' : η * (16 * M) ≤ κ * ε := by
    have hpos : 0 < 48 * M + 16 * ε + 4 * κ := by positivity
    rw [lt_div_iff₀ hpos] at hη4
    nlinarith
  have hWM : W * M ≤ ε / 4 := by
    have : W * M ≤ 4 * η / κ * M := mul_le_mul_of_nonneg_right hWlt.le hM.le
    have e : 4 * η / κ * M = (η * (16 * M)) / (4 * κ) := by field_simp; ring
    rw [e] at this
    have : (η * (16 * M)) / (4 * κ) ≤ κ * ε / (4 * κ) :=
      div_le_div_of_nonneg_right hη' (by positivity)
    have e2 : κ * ε / (4 * κ) = ε / 4 := by field_simp
    linarith
  calc diamond w L * |avgPay g w a j| ≤ (2 * W) * M :=
        mul_le_mul hdia.2 havg (abs_nonneg _) (by positivity)
    _ ≤ ε / 2 := by linarith
