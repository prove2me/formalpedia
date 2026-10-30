-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P15.twisted_bound_dominance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:36:07.852463+00:00
-- url     : https://prove2.me/submissions/47becd94-e9f2-4efc-aa1d-cdfe8cd711d5

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P15

open QAlgorithms.Papers.Independent.Bridge50.P15
open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

theorem s110_tb_therm (N : ℝ) (hN : 0 ≤ N) : 0 ≤ thermalEntropyBits N := by
  unfold thermalEntropyBits
  have h1 : 0 ≤ Real.logb 2 (1 + N) := Real.logb_nonneg (by norm_num) (by linarith)
  rcases hN.lt_or_eq with hp | h0
  · have h2 : Real.logb 2 N ≤ Real.logb 2 (1 + N) :=
      Real.logb_le_logb_of_le (by norm_num) hp (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h2 hN]
  · subst h0; simp

theorem solution (eta N : ℝ) (heta : 0 < eta) (heta1 : eta < 1)
    (hN : 0 ≤ N) (hprime : 0 < eta - N * (1 - eta)) :
    twistedBound eta N ≤ extendedBound eta N ∧ twistedBound eta N ≤ swatBound eta N := by
  have hA : 0 < 1 - eta := by linarith
  have hB : 0 < 1 + N := by linarith
  have hpos : 0 < (eta - N * (1 - eta)) / ((1 + N) * (1 - eta)) := by positivity
  have key : (eta - N * (1 - eta)) / ((1 + N) * (1 - eta)) ≤ (eta / (1 - eta)) / (N + 1) := by
    rw [show (eta / (1 - eta)) / (N + 1) = eta / ((1 + N) * (1 - eta)) by
      field_simp; ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hL : Real.logb 2 ((eta - N * (1 - eta)) / ((1 + N) * (1 - eta))) ≤
      Real.logb 2 (eta / (1 - eta)) - Real.logb 2 (N + 1) := by
    rw [← Real.logb_div (by positivity) (by linarith)]
    exact Real.logb_le_logb_of_le (by norm_num) hpos key
  have hsw : twistedBound eta N ≤ swatBound eta N := by
    unfold twistedBound swatBound
    exact max_le_max le_rfl hL
  refine ⟨le_trans hsw ?_, hsw⟩
  unfold swatBound extendedBound
  apply max_le_max le_rfl
  have h1 : 0 ≤ Real.logb 2 (N + 1) := Real.logb_nonneg (by norm_num) (by linarith)
  have h2 := s110_tb_therm N hN
  linarith
