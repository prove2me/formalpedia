-- Prove2me | solution 1 for StochasticRewardMatching.Decomposable.lemma_5
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:27:58.935118+00:00
-- url     : https://prove2.me/submissions/b0b729f3-22c0-42a5-8899-4116f7fcb425

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_Dual
import Definitions.Def_StochasticRewardMatching_Decomposable_Threshold

open scoped BigOperators
open MeasureTheory Classical
open StochasticRewardMatching.Decomposable

noncomputable section

private lemma le_maxWithZero {xs : List ℝ} {x : ℝ} (hx : x ∈ xs) :
    x ≤ maxWithZero xs := by
  induction xs with
  | nil => simp at hx
  | cons a rest ih =>
    simp only [maxWithZero] at ih ⊢
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact le_max_left x (rest.foldr max 0)
    · exact le_trans (ih hmem) (le_max_right a (rest.foldr max 0))

private def instI1 : Instance 2 1 where
  edges := Finset.univ
  reward i := if i = 0 then 1 else 0
  probability p := if p.1 = 0 then 1 / 2 else 1
  reward_nonneg i := by split_ifs <;> norm_num
  probability_mem e _ := by split_ifs <;> constructor <;> norm_num

private def edgeI1 : Edge instI1 := ⟨(0, 0), Finset.mem_univ _⟩
private def outI1 : Outcome instI1 := fun _ => false
private def seedsI1 : Seeds 2 := fun _ => 0

private lemma threshold_instI1 : threshold instI1 edgeI1 outI1 seedsI1 = 0 := by
  unfold threshold
  set N := reducedNeighbors instI1 edgeI1 outI1 seedsI1
  set rhs := maxWithZero (N.toList.map (fun j => instI1.probability (j, edgeI1.val.2) * (1 - g (seedsI1 j))))
  set roots := {y : ℝ | y ∈ Set.Icc (0 : ℝ) 1 ∧
    instI1.probability edgeI1.val * instI1.reward edgeI1.val.1 * (1 - g y) = rhs}
  have h1_mem : (1 : Fin 2) ∈ N := by
    simp [N, reducedNeighbors, neighbors, algorithmRun, instI1, edgeI1]
  have hN_ne : N ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨1, h1_mem⟩
  have hrhs_ge : 1 - g 0 ≤ rhs := by
    have hmem_map : instI1.probability (1, edgeI1.val.2) * (1 - g (seedsI1 1)) ∈
        N.toList.map (fun j => instI1.probability (j, edgeI1.val.2) * (1 - g (seedsI1 j))) :=
      List.mem_map.mpr ⟨1, Finset.mem_toList.mpr h1_mem, rfl⟩
    have hle := le_maxWithZero hmem_map
    have hval : instI1.probability (1, edgeI1.val.2) * (1 - g (seedsI1 1)) = 1 - g 0 := by
      simp [instI1, seedsI1]
    linarith
  have hg0_lt : g 0 < 1 := by
    unfold g
    calc Real.exp (0 - 1) < Real.exp 0 := Real.exp_lt_exp.mpr (by norm_num)
    _ = 1 := Real.exp_zero
  have hroots_empty : ¬ roots.Nonempty := by
    rintro ⟨y, hy_mem, hy_eq⟩
    have hy0 : 0 ≤ y := hy_mem.1
    have hgy : g 0 ≤ g y := by
      unfold g
      exact Real.exp_le_exp.mpr (by linarith)
    have hcoef : instI1.probability edgeI1.val * instI1.reward edgeI1.val.1 = 1 / 2 := by
      simp [instI1, edgeI1]
    rw [hcoef] at hy_eq
    linarith
  change (if N = ∅ then 1 else if roots.Nonempty then sSup roots else 0) = 0
  rw [if_neg hN_ne, if_neg hroots_empty]

private lemma lambdaPath_instI1_zero (w : Outcome instI1) :
    lambdaPath instI1 w (Function.update seedsI1 edgeI1.val.1 1) edgeI1.val.2 = 0 := by
  unfold lambdaPath
  rw [List.sum_eq_zero]
  intro x hx
  rcases List.mem_map.mp hx with ⟨z, _, rfl⟩
  split_ifs with h
  · cases hz : z.1.2 with
    | none => rfl
    | some i =>
      fin_cases i
      · simp [instI1, edgeI1, g]
      · simp [instI1]
  · rfl

theorem solution : ¬ (∀ {n m : ℕ} (D : Instance n m) (e : Edge D)
    (ω : Outcome D) (Y : Seeds n),
    (∀ j, j ≠ e.val.1 → Y j ∈ Set.Icc (0 : ℝ) 1) →
    (∀ y ∈ Set.Icc (0 : ℝ) 1,
      D.probability e.val * D.reward e.val.1 * (1 - g (threshold D e ω Y)) ≤
        resample D e ω (fun w => lambdaPath D w (Function.update Y e.val.1 y) e.val.2)) ∧
    D.probability e.val * D.reward e.val.1 * (1 - g (threshold D e ω Y)) ≤
      oneSeedAverage e.val.1 Y (fun Z => resample D e ω (fun w => lambdaPath D w Z e.val.2))) := by
  intro hall
  have hY : ∀ j : Fin 2, j ≠ edgeI1.val.1 → seedsI1 j ∈ Set.Icc (0 : ℝ) 1 :=
    fun _ _ => ⟨le_refl 0, zero_le_one⟩
  have h1 := (hall instI1 edgeI1 outI1 seedsI1 hY).1 1 ⟨zero_le_one, le_refl 1⟩
  rw [threshold_instI1] at h1
  have hres : resample instI1 edgeI1 outI1
      (fun w => lambdaPath instI1 w (Function.update seedsI1 edgeI1.val.1 1) edgeI1.val.2) = 0 := by
    unfold resample
    simp [lambdaPath_instI1_zero]
  rw [hres] at h1
  have hcoef : instI1.probability edgeI1.val * instI1.reward edgeI1.val.1 = 1 / 2 := by
    simp [instI1, edgeI1]
  rw [hcoef] at h1
  have hg0_lt : g 0 < 1 := by
    unfold g
    calc Real.exp (0 - 1) < Real.exp 0 := Real.exp_lt_exp.mpr (by norm_num)
    _ = 1 := Real.exp_zero
  linarith
