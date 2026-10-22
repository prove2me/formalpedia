-- Prove2me | solution 1 for OnlineLearningOCO.NormalizedEG.theorem_2_22
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:47:16.238926+00:00
-- url     : https://prove2.me/submissions/1aab3115-d365-4ef1-a134-a9e0ea11ee42

import Mathlib
import Definitions.Def_OnlineLearningOCO_NormalizedEG_Duality
import Definitions.Def_UnderstandingML_Online
import Theorems.Thm_OnlineLearningOCO_NormalizedEG_eq_2_16_2_18
import Theorems.Thm_OnlineLearningOCO_NormalizedEG_bregman_step_bound

open OnlineLearningOCO.NormalizedEG UnderstandingML Finset

theorem solution {d : ℕ} (hd : 0 < d) (η : ℝ) (hη : 0 < η) (z : ℕ → Fin d → ℝ)
    (hz : ∀ t i, -1 ≤ η * z t i) (u : Fin d → ℝ) (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∑ i, u i = 1)
    (T : ℕ) :
    ∑ t ∈ Finset.range T, ∑ i, (wmWeights η z t i - u i) * z t i ≤
      Real.log d / η + η * ∑ t ∈ Finset.range T, ∑ i, wmWeights η z t i * z t i ^ 2 := by
  classical
  let F : ℕ → ℝ := fun t => logSumExpConj η (-(cumSum z t))
  let L : ℕ → ℝ := fun t => ∑ i, wmWeights η z t i*z t i
  let Q : ℕ → ℝ := fun t => ∑ i, wmWeights η z t i*z t i^2
  have hstep (t : ℕ) : L t ≤ F t-F (t+1)+η*Q t := by
    have hb := bregman_step_bound hd η hη z t (hz t)
    rw [(eq_2_16_2_18 hd η hη z t).2.2.1] at hb
    change F (t+1)-F t+L t ≤ η*Q t at hb
    linarith
  have hsum (n : ℕ) : (∑ t ∈ range n, L t) ≤ F 0-F n+η*∑ t ∈ range n, Q t := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, sum_range_succ]
      have hs := hstep n
      linarith
  have hc (n : ℕ) (i : Fin d) : cumSum z n i = ∑ r ∈ range n, z r i := by
    simp [cumSum]
  have hcoord (i : Fin d) : -(cumSum z T i) ≤ F T := by
    have hs : Real.exp (-η*cumSum z T i) ≤ ∑ j, Real.exp (-η*cumSum z T j) :=
      single_le_sum (fun j _ => (Real.exp_pos (-η*cumSum z T j)).le) (mem_univ i)
    have hl := Real.log_le_log (Real.exp_pos _) hs
    rw [Real.log_exp] at hl
    change -(cumSum z T i) ≤ (1/η)*Real.log (∑ j, Real.exp (η*(-cumSum z T j)))
    simp only [mul_neg, ← neg_mul]
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ hη).2
    nlinarith
  have hcomp : -(∑ i, u i*cumSum z T i) ≤ F T := by
    have hs := sum_le_sum (fun i (_ : i ∈ univ) =>
      mul_le_mul_of_nonneg_left (hcoord i) (hu0 i))
    simpa only [mul_neg, sum_neg_distrib, ← sum_mul, hu1, one_mul] using hs
  have hf0 : F 0 = Real.log d / η := by
    simp [F, logSumExpConj, cumSum, div_eq_mul_inv, mul_comm]
  have hreg : (∑ t ∈ range T, ∑ i, (wmWeights η z t i-u i)*z t i) =
      (∑ t ∈ range T, L t) - ∑ i, u i*cumSum z T i := by
    simp only [sub_mul, sum_sub_distrib]
    congr 1
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [hc, mul_sum]
  rw [hreg]
  have hs := hsum T
  rw [hf0] at hs
  change _ ≤ Real.log d / η + η * ∑ t ∈ range T, Q t
  linarith
