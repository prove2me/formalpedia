-- Prove2me | solution 1 for StochasticRewardMatching.Decomposable.lemma_6
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:28:03.629004+00:00
-- url     : https://prove2.me/submissions/8d017cb2-9e69-4e52-adb4-84d01e1d0db2

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_Dual
import Definitions.Def_StochasticRewardMatching_Decomposable_Threshold

open scoped BigOperators
open MeasureTheory Classical
open StochasticRewardMatching.Decomposable

noncomputable section

private lemma bestOf_eq_none {α : Type} (s : α → ℝ) :
    ∀ xs : List α, bestOf s xs = none → xs = []
  | [] => fun _ => rfl
  | a :: rest => by
    unfold bestOf
    cases bestOf s rest with
    | none => simp
    | some b => dsimp; split_ifs <;> simp

private lemma bestOf_le {α : Type} (s : α → ℝ) :
    ∀ (xs : List α) (c : α), bestOf s xs = some c → ∀ x ∈ xs, s x ≤ s c
  | [], _, h => by simp [bestOf] at h
  | a :: rest, c, h => by
    dsimp [bestOf] at h
    cases hrest : bestOf s rest with
    | none =>
      rw [hrest] at h
      dsimp at h
      injection h with hca
      subst hca
      have hnil := bestOf_eq_none s rest hrest
      subst hnil
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact le_refl _
      · simp at hmem
    | some b =>
      rw [hrest] at h
      dsimp at h
      have ih := bestOf_le s rest b hrest
      split_ifs at h with hba <;> injection h with hcb <;> subst hcb
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact le_refl _
        · exact le_trans (ih x hmem) hba
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact le_of_lt (not_le.mp hba)
        · exact ih x hmem

private def instI2 : Instance 2 1 where
  edges := Finset.univ
  reward i := if i = 0 then 1 else 4
  probability _ := 1
  reward_nonneg i := by split_ifs <;> norm_num
  probability_mem _ _ := by constructor <;> norm_num

private def edgeI2 : Edge instI2 := ⟨(0, 0), Finset.mem_univ _⟩
private def outI2 : Outcome instI2 := fun _ => false
private def seedsI2 : Seeds 2 := fun _ => 1 / 2

private lemma decomposable_instI2 : decomposable instI2 :=
  ⟨fun _ => 1, fun _ => 1, fun _ => zero_le_one, fun _ => zero_le_one, fun _ _ => by simp [instI2]⟩

private lemma g_half_le : g (1 / 2) ≤ 2 / 3 := by
  unfold g
  have h1 : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by
    have := Real.add_one_le_exp (1 / 2 : ℝ)
    linarith
  have h2 : Real.exp (1 / 2 - 1) * Real.exp (1 / 2) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have h3 : 0 < Real.exp (1 / 2 - 1) := Real.exp_pos _
  nlinarith

private lemma threshold_instI2 : threshold instI2 edgeI2 outI2 seedsI2 = 1 / 2 := by
  unfold threshold
  set N := reducedNeighbors instI2 edgeI2 outI2 seedsI2
  set rhs := maxWithZero (N.toList.map (fun j => instI2.probability (j, edgeI2.val.2) * (1 - g (seedsI2 j))))
  set roots := {y : ℝ | y ∈ Set.Icc (0 : ℝ) 1 ∧
    instI2.probability edgeI2.val * instI2.reward edgeI2.val.1 * (1 - g y) = rhs}
  have hN : N = {1} := by
    ext i
    fin_cases i <;> simp [N, reducedNeighbors, neighbors, algorithmRun, instI2, edgeI2]
  have hN_ne : N ≠ ∅ := by
    rw [hN]
    exact Finset.singleton_ne_empty 1
  have hrhs : rhs = 1 - g (1 / 2) := by
    have hg_le1 : g (1 / 2) ≤ 1 := le_trans g_half_le (by norm_num)
    simp [rhs, hN, maxWithZero, instI2, seedsI2]
    simpa using hg_le1
  have hroots : roots = {1 / 2} := by
    ext y
    simp only [roots, Set.mem_ofPred_eq, Set.mem_singleton_iff, instI2, edgeI2, hrhs,
       ↓reduceIte, one_mul]
    constructor
    · rintro ⟨_, heq⟩
      have hgy : g y = g (1 / 2) := by linarith
      unfold g at hgy
      have hinj := Real.exp_injective hgy
      linarith
    · rintro rfl
      exact ⟨⟨by norm_num, by norm_num⟩, rfl⟩
  have hroots_ne : roots.Nonempty := by
    rw [hroots]
    exact Set.singleton_nonempty (1 / 2)
  change (if N = ∅ then 1 else if roots.Nonempty then sSup roots else 0) = 1 / 2
  rw [if_neg hN_ne, if_pos hroots_ne, hroots, csSup_singleton]

private lemma choice_instI2_ne_zero (y : ℝ) :
    algorithmChoice instI2 (Function.update seedsI2 edgeI2.val.1 y) Finset.univ 0 ≠ some 0 := by
  unfold algorithmChoice
  intro hchoice
  have h1_mem : (1 : Fin 2) ∈ (neighbors instI2 Finset.univ 0).sort (· ≤ ·) := by
    rw [Finset.mem_sort]
    simp [neighbors, instI2]
  have hle := bestOf_le (score instI2 (Function.update seedsI2 edgeI2.val.1 y) 0) _ 0 hchoice 1 h1_mem
  have hs0 : score instI2 (Function.update seedsI2 edgeI2.val.1 y) 0 0 < 1 := by
    unfold score
    simp only [instI2, edgeI2, ↓reduceIte, Function.update_self, one_mul]
    have hexp : 0 < g y := Real.exp_pos _
    linarith
  have hs1 : (4 / 3 : ℝ) ≤ score instI2 (Function.update seedsI2 edgeI2.val.1 y) 0 1 := by
    unfold score
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [instI2, edgeI2, one_mul]
    rw [Function.update_of_ne hne]
    have h4 : (if (1 : Fin 2) = 0 then (1 : ℝ) else 4) = 4 := by norm_num
    rw [h4]
    change 4 / 3 ≤ 4 * (1 - g (1 / 2))
    linarith [g_half_le]
  linarith

private lemma thetaPath_instI2_zero (w : Outcome instI2) (y : ℝ) :
    thetaPath instI2 w (Function.update seedsI2 edgeI2.val.1 y) edgeI2.val.1 = 0 := by
  unfold thetaPath algorithmHistory
  have hrun : (algorithmRun instI2 (Function.update seedsI2 edgeI2.val.1 y) w Finset.univ 1).2 =
      [((0, algorithmChoice instI2 (Function.update seedsI2 edgeI2.val.1 y) Finset.univ 0),
        actionBit instI2 w (0, algorithmChoice instI2 (Function.update seedsI2 edgeI2.val.1 y) Finset.univ 0))] := by
    rfl
  rw [hrun]
  have hne : algorithmChoice instI2 (Function.update seedsI2 edgeI2.val.1 y) Finset.univ 0 ≠
      some edgeI2.val.1 := choice_instI2_ne_zero y
  simp [hne]

theorem solution : ¬ (∀ {n m : ℕ} (D : Instance n m), decomposable D →
    ∀ (e : Edge D) (ω : Outcome D) (Y : Seeds n),
    (∀ j, j ≠ e.val.1 → Y j ∈ Set.Icc (0 : ℝ) 1) →
    D.probability e.val * D.reward e.val.1 * (∫ x in (0 : ℝ)..threshold D e ω Y, g x) ≤
      oneSeedAverage e.val.1 Y (fun Z => resample D e ω (fun w => thetaPath D w Z e.val.1 * indicator w e))) := by
  intro hall
  have hY : ∀ j : Fin 2, j ≠ edgeI2.val.1 → seedsI2 j ∈ Set.Icc (0 : ℝ) 1 :=
    fun _ _ => ⟨by norm_num [seedsI2], by norm_num [seedsI2]⟩
  have h := hall instI2 decomposable_instI2 edgeI2 outI2 seedsI2 hY
  rw [threshold_instI2] at h
  have hrhs : oneSeedAverage edgeI2.val.1 seedsI2
      (fun Z => resample instI2 edgeI2 outI2 (fun w => thetaPath instI2 w Z edgeI2.val.1 * indicator w edgeI2)) = 0 := by
    unfold oneSeedAverage resample
    simp [thetaPath_instI2_zero]
  rw [hrhs] at h
  have hcoef : instI2.probability edgeI2.val * instI2.reward edgeI2.val.1 = 1 := by
    simp [instI2, edgeI2]
  rw [hcoef, one_mul] at h
  have hg_cont : Continuous g := by
    unfold g
    exact Real.continuous_exp.comp (continuous_id.sub continuous_const)
  have hint_ge : ∫ x in (0 : ℝ)..(1 / 2), g 0 ≤ ∫ x in (0 : ℝ)..(1 / 2), g x := by
    refine intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
      (hg_cont.intervalIntegrable _ _) (fun x hx => ?_)
    unfold g
    exact Real.exp_le_exp.mpr (by linarith [hx.1])
  have hint_const : ∫ x in (0 : ℝ)..(1 / 2), g 0 = (1 / 2) * g 0 := by
    simp [intervalIntegral.integral_const]
  have hg0_pos : 0 < g 0 := Real.exp_pos _
  linarith
