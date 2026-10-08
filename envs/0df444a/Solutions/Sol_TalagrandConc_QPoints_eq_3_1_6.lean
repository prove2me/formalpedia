-- Prove2me | solution 1 for TalagrandConc.QPoints.eq_3_1_6
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:03:01.775793+00:00
-- url     : https://prove2.me/submissions/092426d4-0acf-4211-86a3-960fd895c980

import Mathlib
import Definitions.Def_TalagrandConc_QPoints_Basic



namespace TalagrandConc.QPoints

open scoped ENNReal
open Classical

lemma uncaptured_eq_sum {Ω : Type*} {N q : ℕ} (y : Fin q → Fin N → Ω) (x : Fin N → Ω) :
    uncaptured y x = ∑ i : Fin N, (if ∀ j : Fin q, x i ≠ y j i then 1 else 0) := by
  unfold uncaptured
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

lemma uncaptured_snoc {Ω : Type*} {N q : ℕ} (y' : Fin q → Fin N → Ω) (ω' : Fin q → Ω)
    (x : Fin N → Ω) (ω : Ω) :
    uncaptured (fun j => (Fin.snoc (y' j) (ω' j) : Fin (N + 1) → Ω))
        (Fin.snoc x ω : Fin (N + 1) → Ω) =
      uncaptured y' x + (if ∀ j : Fin q, ω ≠ ω' j then 1 else 0) := by
  rw [uncaptured_eq_sum, uncaptured_eq_sum, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

lemma qDist_le_of_mem {Ω : Type*} {N q : ℕ} (A : Fin q → Set (Fin N → Ω)) (x : Fin N → Ω)
    (y : Fin q → Fin N → Ω) (hy : ∀ j, y j ∈ A j) : qDist A x ≤ (uncaptured y x : ℕ∞) := by
  unfold qDist
  exact iInf₂_le y hy

lemma le_qDist {Ω : Type*} {N q : ℕ} (A : Fin q → Set (Fin N → Ω)) (x : Fin N → Ω) (c : ℕ∞)
    (h : ∀ y : Fin q → Fin N → Ω, (∀ j, y j ∈ A j) → c ≤ (uncaptured y x : ℕ∞)) :
    c ≤ qDist A x := by
  unfold qDist
  exact le_iInf₂ h

lemma qDist_anti {Ω : Type*} {N q : ℕ} (A A' : Fin q → Set (Fin N → Ω)) (x : Fin N → Ω)
    (h : ∀ i, A i ⊆ A' i) : qDist A' x ≤ qDist A x := by
  apply le_qDist
  intro y hy
  exact qDist_le_of_mem A' x y (fun j => h j (hy j))

theorem eq_3_1_6_core {Ω : Type*} {N q : ℕ} (hq : 2 ≤ q) (A : Fin q → Set (Fin (N + 1) → Ω))
    (x : Fin N → Ω) (ω : Ω) :
    qDist A (Fin.snoc x ω : Fin (N + 1) → Ω) ≤ 1 + qDist (fun i => projLast (A i)) x ∧
      ∀ j : Fin q, qDist A (Fin.snoc x ω : Fin (N + 1) → Ω) ≤
        qDist (Function.update (fun i => projLast (A i)) j (sliceAt (A j) ω)) x := by
  classical
  constructor
  · unfold qDist
    rw [ENat.add_iInf₂]
    refine le_iInf₂ fun y' hy' => ?_
    choose ω' hω' using hy'
    refine le_trans (iInf₂_le (fun j => (Fin.snoc (y' j) (ω' j) : Fin (N + 1) → Ω)) hω') ?_
    rw [uncaptured_snoc]
    push_cast
    split_ifs <;> simp [add_comm]
  · intro j
    apply le_qDist
    intro y' hy'
    have hj : y' j ∈ sliceAt (A j) ω := by simpa using hy' j
    have hother : ∀ i, i ≠ j → y' i ∈ projLast (A i) := by
      intro i hi
      have := hy' i
      rwa [Function.update_of_ne hi] at this
    let ω' : Fin q → Ω := fun i => if h : i = j then ω else Classical.choose (hother i h)
    have hmem : ∀ i, (Fin.snoc (y' i) (ω' i) : Fin (N + 1) → Ω) ∈ A i := by
      intro i
      by_cases h : i = j
      · subst h
        simp only [ω', dif_pos]
        exact hj
      · simp only [ω', dif_neg h]
        exact Classical.choose_spec (hother i h)
    refine le_trans (qDist_le_of_mem A _ _ hmem) ?_
    rw [uncaptured_snoc]
    have : ¬ ∀ i : Fin q, ω ≠ ω' i := by
      push Not
      exact ⟨j, by simp [ω']⟩
    simp [this]

end TalagrandConc.QPoints

open TalagrandConc.QPoints


theorem solution {Ω : Type*} {N q : ℕ} (hq : 2 ≤ q) (A : Fin q → Set (Fin (N + 1) → Ω))
    (x : Fin N → Ω) (ω : Ω) :
    qDist A (Fin.snoc x ω : Fin (N + 1) → Ω) ≤ 1 + qDist (fun i => projLast (A i)) x ∧
      ∀ j : Fin q, qDist A (Fin.snoc x ω : Fin (N + 1) → Ω) ≤
        qDist (Function.update (fun i => projLast (A i)) j (sliceAt (A j) ω)) x := by
  exact eq_3_1_6_core hq A x ω
