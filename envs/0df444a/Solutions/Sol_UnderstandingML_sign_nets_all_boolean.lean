-- Prove2me | solution 1 for UnderstandingML.sign_nets_all_boolean
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T12:50:41.630272+00:00
-- url     : https://prove2.me/submissions/c9d240d4-ba98-4872-9a6b-103d399d03af

import Definitions.Def_UnderstandingML_NeuralNetworks

open MeasureTheory

namespace UnderstandingML

lemma signAct_pos_iff (a : ℝ) : signAct a = 1 ↔ 0 < a := by
  unfold signAct; split_ifs with h <;> norm_num [h]

lemma match_sum_pos_iff {n : ℕ} (u x : Fin n → Bool) :
    0 < ∑ j : Fin n, (if u j then (1:ℝ) else -1) * (if x j then (1:ℝ) else -1) + (1 - n) ↔ x = u := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hne
    have hle : ∑ j : Fin n, (if u j then (1:ℝ) else -1) * (if x j then (1:ℝ) else -1)
        ≤ ∑ j : Fin n, (if j = j0 then (-1:ℝ) else 1) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = j0
      · subst hj; cases hu : u j <;> cases hx : x j <;> simp_all
      · cases hu : u j <;> cases hx : x j <;> simp [hj]
    have : ∑ j : Fin n, (if j = j0 then (-1:ℝ) else 1) = n - 2 := by
      rw [Finset.sum_ite]
      simp [Finset.filter_eq', Finset.filter_ne']
      have hn : 1 ≤ n := j0.pos
      rw [Nat.cast_sub hn]; push_cast; ring
    linarith
  · rintro rfl
    have : ∑ j : Fin n, (if x j then (1:ℝ) else -1) * (if x j then (1:ℝ) else -1) = n := by
      rw [Finset.sum_congr rfl (fun j _ => show (if x j then (1:ℝ) else -1) * (if x j then (1:ℝ) else -1) = 1 by
        cases x j <;> norm_num)]
      simp
    linarith


/-- The layer widths `n + 1, 2^n + 1, 1` of the Claim 20.1 network. -/
def claimWidth (n : ℕ) : ℕ → ℕ := fun t => if t = 0 then n + 1 else if t = 1 then 2 ^ n + 1 else 1

noncomputable def claimEquiv (n : ℕ) : (Fin n → Bool) ≃ Fin (2 ^ n) :=
  Fintype.equivFinOfCardEq (by simp)

open Classical in
noncomputable def claimWeights (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ → ℕ → ℕ → ℝ :=
  fun t i j =>
    if t = 0 then
      (if hi : i < 2 ^ n then
        (if hj : j < n then (if (claimEquiv n).symm ⟨i, hi⟩ ⟨j, hj⟩ then 1 else -1) else 1 - n)
      else 0)
    else
      (if hj : j < 2 ^ n then (if f ((claimEquiv n).symm ⟨j, hj⟩) then 1 else 0)
      else 1 - ∑ u : Fin n → Bool, (if f u then (1:ℝ) else 0))

lemma claim_hidden_output (n : ℕ) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (j : ℕ) (hj : j < 2 ^ n) :
    netOutput signAct (LayeredGraph.full 2 (claimWidth n)) (claimWeights n f)
      (inputLayer (fun i ↦ if x i then (1 : ℝ) else -1)) 1 j =
      if x = (claimEquiv n).symm ⟨j, hj⟩ then 1 else -1 := by
  show signAct _ = _
  have hw : (LayeredGraph.full 2 (claimWidth n)).width 0 = n + 1 := by
    simp [LayeredGraph.full, claimWidth]
  rw [hw, Finset.sum_range_succ, Finset.sum_range]
  have e1 : ∀ k : Fin n, (if (j, (k : ℕ)) ∈ (LayeredGraph.full 2 (claimWidth n)).edges 0 then
      claimWeights n f 0 j k else 0) *
      netOutput signAct (LayeredGraph.full 2 (claimWidth n)) (claimWeights n f)
        (inputLayer fun i => if x i = true then 1 else -1) 0 k =
      (if (claimEquiv n).symm ⟨j, hj⟩ k then (1:ℝ) else -1) * (if x k then (1:ℝ) else -1) := by
    intro k
    have hk : (k : ℕ) < n + 1 := Nat.lt_succ_of_lt k.isLt
    simp [LayeredGraph.full, claimWidth, claimWeights, hj, hj.le, inputLayer, netOutput, hk]
  have e2 : (if (j, n) ∈ (LayeredGraph.full 2 (claimWidth n)).edges 0 then
      claimWeights n f 0 j n else 0) *
      netOutput signAct (LayeredGraph.full 2 (claimWidth n)) (claimWeights n f)
        (inputLayer fun i => if x i = true then 1 else -1) 0 n = 1 - n := by
    simp [LayeredGraph.full, claimWidth, claimWeights, hj, hj.le, inputLayer, netOutput]
  rw [Finset.sum_congr rfl (fun k _ => e1 k), e2]
  unfold signAct
  simp only [match_sum_pos_iff]

lemma claim_const_output (n : ℕ) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    netOutput signAct (LayeredGraph.full 2 (claimWidth n)) (claimWeights n f)
      (inputLayer (fun i ↦ if x i then (1 : ℝ) else -1)) 1 (2 ^ n) = -1 := by
  show signAct _ = _
  simp [claimWeights, signAct]

lemma claim_netInput (n : ℕ) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    netInput signAct (LayeredGraph.full 2 (claimWidth n)) (claimWeights n f)
      (inputLayer (fun i ↦ if x i then (1 : ℝ) else -1)) 1 0 = if f x then 1 else -1 := by
  unfold netInput
  have hw : (LayeredGraph.full 2 (claimWidth n)).width 1 = 2 ^ n + 1 := by
    simp [LayeredGraph.full, claimWidth]
  rw [hw, Finset.sum_range_succ, Finset.sum_range, claim_const_output]
  have e1 : ∀ j : Fin (2 ^ n), (if (0, (j : ℕ)) ∈ (LayeredGraph.full 2 (claimWidth n)).edges 1 then
      claimWeights n f 1 0 j else 0) *
      netOutput signAct (LayeredGraph.full 2 (claimWidth n)) (claimWeights n f)
        (inputLayer fun i => if x i = true then 1 else -1) 1 j =
      (fun u => (if f u then (1:ℝ) else 0) * (if x = u then 1 else -1)) ((claimEquiv n).symm j) := by
    intro j
    rw [claim_hidden_output n f x j j.isLt]
    have hj1 : (j : ℕ) < 2 ^ n + 1 := Nat.lt_succ_of_lt j.isLt
    simp [LayeredGraph.full, claimWidth, claimWeights, hj1, j.isLt]
  have e2 : (if (0, 2 ^ n) ∈ (LayeredGraph.full 2 (claimWidth n)).edges 1 then
      claimWeights n f 1 0 (2 ^ n) else 0) * (-1) =
      ∑ u : Fin n → Bool, (if f u then (1:ℝ) else 0) - 1 := by
    simp [LayeredGraph.full, claimWidth, claimWeights]
  rw [Finset.sum_congr rfl (fun j _ => e1 j), e2, Equiv.sum_comp (claimEquiv n).symm
    (fun u => (if f u then (1:ℝ) else 0) * (if x = u then 1 else -1))]
  have e3 : ∀ u : Fin n → Bool, (if f u then (1:ℝ) else 0) * (if x = u then 1 else -1) =
      2 * (if u = x then (if f u then (1:ℝ) else 0) else 0) - (if f u then (1:ℝ) else 0) := by
    intro u
    by_cases h : u = x
    · subst h; cases f u <;> norm_num
    · rw [if_neg (Ne.symm h), if_neg h]; ring
  rw [Finset.sum_congr rfl (fun u _ => e3 u), Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  cases f x
  · norm_num; ring
  · norm_num

theorem sign_nets_all_boolean_aux (n : ℕ) :
    ∃ G : LayeredGraph, G.depth = 2 ∧ G.width 0 = n + 1 ∧ G.width 1 = 2 ^ n + 1 ∧
      G.width 2 = 1 ∧ G.numEdges = (n + 1) * (2 ^ n + 1) + (2 ^ n + 1) ∧
      ∀ f : (Fin n → Bool) → Bool, ∃ h ∈ signNetClass n G,
        ∀ x : Fin n → Bool, h (fun i ↦ if x i then (1 : ℝ) else -1) = f x := by
  refine ⟨LayeredGraph.full 2 (claimWidth n), rfl, by simp [LayeredGraph.full, claimWidth],
    by simp [LayeredGraph.full, claimWidth], by simp [LayeredGraph.full, claimWidth], ?_, ?_⟩
  · simp [LayeredGraph.numEdges, LayeredGraph.full, claimWidth, Finset.sum_range_succ]
    ring
  · intro f
    refine ⟨_, ⟨claimWeights n f, rfl⟩, fun x => ?_⟩
    show decide (0 < netInput signAct _ _ _ (2 - 1) 0) = f x
    rw [show 2 - 1 = 1 from rfl, claim_netInput]
    cases f x <;> norm_num

end UnderstandingML

open UnderstandingML in
theorem solution (n : ℕ) :
    ∃ G : LayeredGraph, G.depth = 2 ∧ G.width 0 = n + 1 ∧ G.width 1 = 2 ^ n + 1 ∧
      G.width 2 = 1 ∧ G.numEdges = (n + 1) * (2 ^ n + 1) + (2 ^ n + 1) ∧
      ∀ f : (Fin n → Bool) → Bool, ∃ h ∈ signNetClass n G,
        ∀ x : Fin n → Bool, h (fun i ↦ if x i then (1 : ℝ) else -1) = f x :=
  sign_nets_all_boolean_aux n
