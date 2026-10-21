-- Prove2me | solution 1 for TwoAgentSched.Knapsack.eq_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:26:11.207118+00:00
-- url     : https://prove2.me/submissions/a1376895-d01f-4105-9f53-f09b84ff0d0f

import Mathlib
import Definitions.Def_TwoAgentSched_Knapsack_Construction

set_option autoImplicit false
open TwoAgentSched.Knapsack MooreLateJobs.Shared

lemma kn_ct_eq {ι : Type*} [DecidableEq ι] [Fintype ι] (t : ι → ℝ) (l : List ι)
    (hl : IsSchedule Finset.univ l) (j : ι) :
    completionTime t l j = ∑ y, if l.idxOf y ≤ l.idxOf j then t y else 0 := by
  have hj : j ∈ l := (hl.2 j).2 (Finset.mem_univ j)
  unfold completionTime completionAt
  have hnd' : (l.take (l.idxOf j + 1)).Nodup := hl.1.sublist (List.take_sublist _ _)
  rw [← List.sum_toFinset _ hnd', ← Finset.sum_filter]
  congr 1
  ext y
  have hyl : y ∈ l := (hl.2 y).2 (Finset.mem_univ y)
  simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [List.mem_take_iff_idxOf_lt hyl]
  omega

instance kn_sumLawfulBEq {α β : Type*} [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] :
    LawfulBEq (α ⊕ β) where
  eq_of_beq := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b <;> simp_all [BEq.beq, Sum.instBEq.beq]
  rfl := by
    intro a
    rcases a with a | a <;> simp [BEq.beq, Sum.instBEq.beq]

theorem kn_sumBEq_eq {α β : Type*} [DecidableEq α] [DecidableEq β] :
    (Sum.instBEq : BEq (α ⊕ β)) = instBEqOfDecidableEq := by
  have : ∀ a b : α ⊕ β, (Sum.instBEq : BEq (α ⊕ β)).beq a b = (instBEqOfDecidableEq : BEq (α ⊕ β)).beq a b := by
    intro a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [BEq.beq, Sum.instBEq.beq]
  cases h1 : (Sum.instBEq : BEq (α ⊕ β)) with
  | mk f =>
    cases h2 : (instBEqOfDecidableEq : BEq (α ⊕ β)) with
    | mk g =>
      have e : f = g := by
        funext a b
        have := this a b
        rw [h1, h2] at this
        exact this
      rw [e]

namespace KN
variable {n : ℕ} (u w : Fin n → ℕ)

abbrev Jb := Fin (construction u w).nA ⊕ Fin (construction u w).nB

lemma kn_ct_eq' (l : List (Jb u w)) (hl : IsSchedule Finset.univ l) (j : Jb u w) :
    completionTime (construction u w).p l j =
      ∑ y, if l.idxOf y ≤ l.idxOf j then (construction u w).p y else 0 := by
  rw [kn_ct_eq _ l hl]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [kn_sumBEq_eq]

def bI : Fin (construction u w).nB := ⟨0, Nat.one_pos⟩

lemma sum_nB (g : Fin (construction u w).nB → ℝ) :
    ∑ k, g k = g (bI u w) := by
  rw [Finset.sum_eq_single (bI u w)]
  · intro b _ hb
    exfalso; apply hb; apply Fin.ext
    have := b.2
    simp only [construction] at this ⊢
    omega
  · intro h; exact absurd (Finset.mem_univ _) h

lemma tA (i : Fin n) : (construction u w).p (aJob u w i) = (u i : ℝ) := rfl
lemma tB (k : Fin (construction u w).nB) : (construction u w).p (Sum.inr k) = (pB1 u w : ℝ) := rfl

lemma idx_ne (l : List (Jb u w)) (hl : IsSchedule Finset.univ l) (i : Fin n) :
    l.idxOf (aJob u w i) ≠ l.idxOf (bJob u w) := by
  intro h
  have hai : aJob u w i ∈ l := (hl.2 _).2 (Finset.mem_univ _)
  have := (List.idxOf_inj hai).1 h
  exact absurd this (by simp [aJob, bJob])

/-- completion time of the B-job -/
lemma CB (l : List (Jb u w)) (hl : IsSchedule Finset.univ l) :
    (construction u w).C l (bJob u w) = (pB1 u w : ℝ) +
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => l.idxOf (aJob u w i) < l.idxOf (bJob u w)),
        (u i : ℝ) := by
  unfold Instance.C
  rw [kn_ct_eq' u w l hl, Fintype.sum_sum_type, sum_nB, Finset.sum_filter]
  have hbb : (Sum.inr (bI u w) : Jb u w) = bJob u w := rfl
  rw [hbb, if_pos le_rfl, add_comm]
  rw [show (construction u w).p (bJob u w) = (pB1 u w : ℝ) from rfl]
  congr 1
  refine Finset.sum_congr rfl (fun (i : Fin n) _ => ?_)
  have hne := idx_ne u w l hl i
  have e1 : l.idxOf (Sum.inl i : Jb u w) = l.idxOf (aJob u w i) := rfl
  rw [e1]
  by_cases h : l.idxOf (aJob u w i) < l.idxOf (bJob u w)
  · rw [if_pos h.le, if_pos h]; rfl
  · rw [if_neg (fun h' => h (lt_of_le_of_ne h' hne)), if_neg h]

lemma CA_bounds (l : List (Jb u w)) (hl : IsSchedule Finset.univ l) (i : Fin n) :
    (u i : ℝ) + (if l.idxOf (aJob u w i) < l.idxOf (bJob u w) then 0 else (pB1 u w : ℝ)) ≤
        (construction u w).C l (aJob u w i) ∧
      (construction u w).C l (aJob u w i) ≤
        (uHat u : ℝ) + (if l.idxOf (aJob u w i) < l.idxOf (bJob u w) then 0 else (pB1 u w : ℝ)) := by
  unfold Instance.C
  rw [kn_ct_eq' u w l hl, Fintype.sum_sum_type, sum_nB]
  have hbi : (l.idxOf (Sum.inr (bI u w) : Jb u w) ≤ l.idxOf (aJob u w i)) ↔
      ¬ (l.idxOf (aJob u w i) < l.idxOf (bJob u w)) := by
    rw [not_lt]; rfl
  have hB : (if l.idxOf (Sum.inr (bI u w) : Jb u w) ≤ l.idxOf (aJob u w i) then
        (construction u w).p (Sum.inr (bI u w)) else 0) =
      (if l.idxOf (aJob u w i) < l.idxOf (bJob u w) then 0 else (pB1 u w : ℝ)) := by
    by_cases h : l.idxOf (aJob u w i) < l.idxOf (bJob u w)
    · rw [if_neg (fun h' => (hbi.1 h') h), if_pos h]
    · rw [if_pos (hbi.2 h), if_neg h]; rfl
  rw [hB]
  have hnn : ∀ y : Jb u w, 0 ≤ (construction u w).p y := by
    intro y; rcases y with y | y
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
  constructor
  · have h1 : (u i : ℝ) ≤ ∑ a, if l.idxOf (Sum.inl a : Jb u w) ≤ l.idxOf (aJob u w i) then
        (construction u w).p (Sum.inl a) else 0 := by
      have := Finset.single_le_sum (f := fun a : Fin n => if l.idxOf (Sum.inl a : Jb u w) ≤
          l.idxOf (aJob u w i) then (construction u w).p (Sum.inl a) else 0)
        (fun a _ => by split_ifs; exact hnn _; exact le_refl _) (Finset.mem_univ i)
      have e : (if l.idxOf (Sum.inl i : Jb u w) ≤ l.idxOf (aJob u w i) then
          (construction u w).p (Sum.inl i) else 0) = (u i : ℝ) := by
        have e1 : l.idxOf (Sum.inl i : Jb u w) = l.idxOf (aJob u w i) := rfl
        rw [e1, if_pos (le_refl _)]; rfl
      rw [e] at this; exact this
    linarith
  · have h1 : (∑ a, if l.idxOf (Sum.inl a : Jb u w) ≤ l.idxOf (aJob u w i) then
        (construction u w).p (Sum.inl a) else 0) ≤ (uHat u : ℝ) := by
      unfold uHat; push_cast
      refine Finset.sum_le_sum (fun a _ => ?_)
      split_ifs
      · exact le_refl _
      · exact Nat.cast_nonneg _
    linarith

end KN

namespace KN
variable {n : ℕ} (u w : Fin n → ℕ)

lemma inr_eq_b (k : Fin (construction u w).nB) : (Sum.inr k : Jb u w) = bJob u w := by
  have : k = bI u w := by
    apply Fin.ext
    have := k.2
    simp only [construction] at this
    simp [bI]; omega
  rw [this]; rfl

lemma wsum_eq (S : Finset (Fin n)) :
    ∑ i, (w i : ℝ) * ((uHat u : ℝ) + (if i ∈ S then 0 else (pB1 u w : ℝ))) =
      (wHat w : ℝ) * (uHat u : ℝ) + (pB1 u w : ℝ) * ((wHat w : ℝ) - ∑ i ∈ S, (w i : ℝ)) := by
  have h1 : ∀ i, (w i : ℝ) * ((uHat u : ℝ) + (if i ∈ S then 0 else (pB1 u w : ℝ))) =
      (w i : ℝ) * (uHat u : ℝ) + ((pB1 u w : ℝ) * (w i : ℝ) -
        (if i ∈ S then (pB1 u w : ℝ) * (w i : ℝ) else 0)) := by
    intro i; split_ifs <;> ring
  simp_rw [h1]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]
  unfold wHat; push_cast; ring

end KN

open KN in
theorem solution {n : ℕ} (u w : Fin n → ℕ) (b W : ℤ) (S : Finset (Fin n))
    (hu : ((∑ i ∈ S, u i : ℕ) : ℤ) ≤ b) (hw : W ≤ ((∑ i ∈ S, w i : ℕ) : ℤ))
    (l : List (Fin (construction u w).nA ⊕ Fin (construction u w).nB))
    (hl : MooreLateJobs.Shared.IsSchedule Finset.univ l)
    (hS : ∀ i : Fin n, i ∈ S ↔ l.idxOf (aJob u w i) < l.idxOf (bJob u w)) :
    (construction u w).Meets ((QA u w W : ℤ) : ℝ) ((QB u w b : ℤ) : ℝ) l := by
  have hSeq : S = Finset.univ.filter (fun i : Fin n => l.idxOf (aJob u w i) < l.idxOf (bJob u w)) := by
    ext i; rw [Finset.mem_filter]; simp [hS i]
  refine ⟨hl, ?_, ?_⟩
  · unfold Instance.sumWC
    have hCi : ∀ i : Fin n, (construction u w).C l (Sum.inl i) ≤
        (uHat u : ℝ) + (if i ∈ S then 0 else (pB1 u w : ℝ)) := by
      intro i
      have := (CA_bounds u w l hl i).2
      have e : (if l.idxOf (aJob u w i) < l.idxOf (bJob u w) then (0 : ℝ) else (pB1 u w : ℝ)) =
          (if i ∈ S then 0 else (pB1 u w : ℝ)) := by
        by_cases h : i ∈ S
        · rw [if_pos h, if_pos ((hS i).1 h)]
        · rw [if_neg h, if_neg (fun h' => h ((hS i).2 h'))]
      rw [e] at this; exact this
    have hwS : (W : ℝ) ≤ ∑ i ∈ S, (w i : ℝ) := by
      have : (W : ℝ) ≤ ((∑ i ∈ S, w i : ℕ) : ℝ) := by exact_mod_cast hw
      simpa using this
    calc ∑ h, ((construction u w).wA h : ℝ) * (construction u w).C l (Sum.inl h)
        ≤ ∑ i : Fin n, (w i : ℝ) * ((uHat u : ℝ) + (if i ∈ S then 0 else (pB1 u w : ℝ))) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hCi i) (Nat.cast_nonneg _))
      _ = (wHat w : ℝ) * (uHat u : ℝ) + (pB1 u w : ℝ) * ((wHat w : ℝ) - ∑ i ∈ S, (w i : ℝ)) :=
          wsum_eq u w S
      _ ≤ ((QA u w W : ℤ) : ℝ) := by
          unfold QA
          push_cast
          have hP : (0 : ℝ) ≤ (pB1 u w : ℝ) := Nat.cast_nonneg _
          nlinarith
  · intro k
    rw [inr_eq_b u w k, CB u w l hl, ← hSeq]
    unfold QB
    push_cast
    have : ((∑ i ∈ S, u i : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hu
    push_cast at this
    linarith
