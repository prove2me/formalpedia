-- Prove2me | solution 1 for SuttonBartoRL.BatchTD.you_are_the_predictor
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T18:31:19.937764+00:00
-- url     : https://prove2.me/submissions/765ee44a-3f25-44c7-a091-d3521d087a51

import Mathlib
import Definitions.Def_SuttonBartoRL_BatchTD_Episodes
import Definitions.Def_SuttonBartoRL_BatchTD_BatchUpdating

open Filter Topology
open SuttonBartoRL.BatchTD

noncomputable abbrev bb : Batch (Fin 2) :=
      [[((0 : Fin 2), (0 : ℝ)), (1, 0)], [(1, 1)], [(1, 1)], [(1, 1)], [(1, 1)], [(1, 1)],
        [(1, 1)], [(1, 0)]]

lemma vc0 : visitCount bb 0 = 1 := by decide
lemma vc1 : visitCount bb 1 = 8 := by decide
lemma tc (s : Fin 2) (j : Option (Fin 2)) : transCount bb s j =
   if s = 0 ∧ j = some 1 then 1 else if s = 1 ∧ j = none then 8 else 0 := by
  fin_cases s <;> rcases j with _ | j <;> try fin_cases j
  all_goals decide

lemma td (V : Fin 2 → ℝ) : tdIncrement 1 bb V 0 = V 1 - V 0 ∧ tdIncrement 1 bb V 1 = 6 - 8 * V 1 := by
  simp [tdIncrement, visitSum, tdError, stateAt, nextReward, extV, Finset.sum_range_succ]
  ring

lemma mc (V : Fin 2 → ℝ) : mcIncrement 1 bb V 0 = - V 0 ∧ mcIncrement 1 bb V 1 = 6 - 8 * V 1 := by
  simp [mcIncrement, visitSum, ret, stateAt, nextReward, extV, Finset.sum_range_succ]
  ring

lemma avg : mcAverage 1 bb 0 = 0 ∧ mcAverage 1 bb 1 = 3/4 := by
  simp [mcAverage, visitSum, ret, stateAt, nextReward, Finset.sum_range_succ, vc0, vc1]
  norm_num

lemma trs0 : transRewardSum bb 0 (some 1) = 0 := by
  simp [transRewardSum, visitSum, stateAt, nextReward, Finset.sum_range_succ]
lemma trs1 : transRewardSum bb 1 none = 6 := by
  simp [transRewardSum, visitSum, stateAt, nextReward, Finset.sum_range_succ]; norm_num

lemma rhat : mlExpectedReward bb = ![0, 3/4] := by
  funext s; fin_cases s <;>
  simp [mlExpectedReward, mlProb, mlReward, tc, vc0, vc1, Fintype.sum_option, trs0, trs1] <;> norm_num

lemma Phat : mlMatrix bb = !![0, 1; 0, 0] := by
  ext s j; fin_cases s <;> fin_cases j <;> simp [mlMatrix, mlProb, tc, vc0, vc1]

lemma Ppow (k : ℕ) : mlMatrix bb ^ (k + 2) = 0 := by
  rw [pow_add, Phat]
  have : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
  rw [this, mul_zero]

lemma ce (s : Fin 2) : ceEstimate 1 bb s = 3/4 := by
  unfold ceEstimate
  rw [tsum_eq_sum (s := Finset.range 2)]
  · rw [Finset.sum_range_succ, Finset.sum_range_one]
    fin_cases s <;> simp [rhat, Phat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [Ppow]; simp

lemma tdIt (α : ℝ) (V₀ : Fin 2 → ℝ) (m : ℕ) :
    batchTD α 1 bb V₀ m 1 = 3/4 + (1 - 8*α)^m * (V₀ 1 - 3/4) ∧
    batchTD α 1 bb V₀ m 0 = 3/4 + (1 - α)^m * (V₀ 0 - 3/4)
      + (V₀ 1 - 3/4) * ((1-α)^m - (1-8*α)^m) / 7 := by
  induction m with
  | zero => simp [batchTD]
  | succ m ih =>
    have e : batchTD α 1 bb V₀ (m+1) = batchTDStep α 1 bb (batchTD α 1 bb V₀ m) := by
      simp only [batchTD]; rw [Function.iterate_succ_apply']
    rw [e]; simp only [batchTDStep, (td _).1, (td _).2, ih.1, ih.2]
    constructor <;> ring

lemma mcIt (α : ℝ) (V₀ : Fin 2 → ℝ) (m : ℕ) :
    batchMC α 1 bb V₀ m 1 = 3/4 + (1 - 8*α)^m * (V₀ 1 - 3/4) ∧
    batchMC α 1 bb V₀ m 0 = (1 - α)^m * V₀ 0 := by
  induction m with
  | zero => simp [batchMC]
  | succ m ih =>
    have e : batchMC α 1 bb V₀ (m+1) = batchMCStep α 1 bb (batchMC α 1 bb V₀ m) := by
      simp only [batchMC]; rw [Function.iterate_succ_apply']
    rw [e]; simp only [batchMCStep, (mc _).1, (mc _).2, ih.1, ih.2]
    constructor <;> ring

theorem solution :
    let b : Batch (Fin 2) :=
      [[((0 : Fin 2), (0 : ℝ)), (1, 0)], [(1, 1)], [(1, 1)], [(1, 1)], [(1, 1)], [(1, 1)],
        [(1, 1)], [(1, 0)]]
    ceEstimate 1 b 0 = 3 / 4 ∧ ceEstimate 1 b 1 = 3 / 4 ∧
    mcAverage 1 b 0 = 0 ∧ mcAverage 1 b 1 = 3 / 4 ∧
    ∃ αbar : ℝ, 0 < αbar ∧ ∀ α : ℝ, 0 < α → α < αbar → ∀ V₀ : Fin 2 → ℝ,
      Tendsto (fun m : ℕ => batchTD α 1 b V₀ m 0) atTop (𝓝 (3 / 4)) ∧
      Tendsto (fun m : ℕ => batchTD α 1 b V₀ m 1) atTop (𝓝 (3 / 4)) ∧
      Tendsto (fun m : ℕ => batchMC α 1 b V₀ m 0) atTop (𝓝 0) ∧
      Tendsto (fun m : ℕ => batchMC α 1 b V₀ m 1) atTop (𝓝 (3 / 4)) := by
  intro b
  change ceEstimate 1 bb 0 = 3 / 4 ∧ ceEstimate 1 bb 1 = 3 / 4 ∧
    mcAverage 1 bb 0 = 0 ∧ mcAverage 1 bb 1 = 3 / 4 ∧
    ∃ αbar : ℝ, 0 < αbar ∧ ∀ α : ℝ, 0 < α → α < αbar → ∀ V₀ : Fin 2 → ℝ,
      Tendsto (fun m : ℕ => batchTD α 1 bb V₀ m 0) atTop (𝓝 (3 / 4)) ∧
      Tendsto (fun m : ℕ => batchTD α 1 bb V₀ m 1) atTop (𝓝 (3 / 4)) ∧
      Tendsto (fun m : ℕ => batchMC α 1 bb V₀ m 0) atTop (𝓝 0) ∧
      Tendsto (fun m : ℕ => batchMC α 1 bb V₀ m 1) atTop (𝓝 (3 / 4))
  refine ⟨ce 0, ce 1, avg.1, avg.2, 1/8, by norm_num, fun α hα hαb V₀ => ?_⟩
  have ha : Tendsto (fun m : ℕ => (1 - α)^m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  have hc : Tendsto (fun m : ℕ => (1 - 8*α)^m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  have hB : Tendsto (fun m : ℕ => 3/4 + (1 - 8*α)^m * (V₀ 1 - 3/4)) atTop (𝓝 (3/4)) := by
    simpa using (hc.mul_const (V₀ 1 - 3/4)).const_add (3/4 : ℝ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [fun m => (tdIt α V₀ m).2]
    have := (((ha.mul_const (V₀ 0 - 3/4)).const_add (3/4 : ℝ)).add
      (((ha.sub hc).const_mul (V₀ 1 - 3/4)).div_const 7))
    simpa using this
  · simp only [fun m => (tdIt α V₀ m).1]; exact hB
  · simp only [fun m => (mcIt α V₀ m).2]; simpa using ha.mul_const (V₀ 0)
  · simp only [fun m => (mcIt α V₀ m).1]; exact hB
