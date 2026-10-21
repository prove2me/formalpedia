-- Prove2me | solution 1 for TwoAgentSched.TotalTotal.eq_5_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:14:04.916806+00:00
-- url     : https://prove2.me/submissions/a6f1d647-01a7-4f0e-8b4c-69e473c74e7a

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_Construction

set_option autoImplicit false
open TwoAgentSched.TotalTotal MooreLateJobs.Shared

section generic
variable {ι : Type*} [DecidableEq ι] (t : ι → ℝ)

lemma ttt_ca_append_left (l₁ l₂ : List ι) (m : ℕ) (hm : m < l₁.length) :
    completionAt t (l₁ ++ l₂) m = completionAt t l₁ m := by
  unfold completionAt
  rw [List.take_append_of_le_length (by omega)]

lemma ttt_ct_append_left (l₁ l₂ : List ι) (x : ι) (hx : x ∈ l₁) :
    completionTime t (l₁ ++ l₂) x = completionTime t l₁ x := by
  unfold completionTime
  rw [List.idxOf_append_of_mem hx]
  exact ttt_ca_append_left t l₁ l₂ _ (List.idxOf_lt_length_iff.mpr hx)

lemma ttt_ct_append_right (l₁ l₂ : List ι) (x : ι) (hx : x ∉ l₁) :
    completionTime t (l₁ ++ l₂) x = (l₁.map t).sum + completionTime t l₂ x := by
  unfold completionTime completionAt
  rw [List.idxOf_append_of_notMem hx, List.take_append]
  have e1 : l₁.take (l₁.length + l₂.idxOf x + 1) = l₁ := List.take_of_length_le (by omega)
  have e3 : l₁.length + l₂.idxOf x + 1 - l₁.length = l₂.idxOf x + 1 := by omega
  rw [e1, e3]
  simp

end generic

namespace TTT

variable {k : ℕ} (p : Fin k → ℕ) (x : Fin k → Bool)

def pr (i : Fin k) : List (Fin k ⊕ Fin k) :=
  if x i then [Sum.inr i, Sum.inl i] else [Sum.inl i, Sum.inr i]

def tt : Fin k ⊕ Fin k → ℝ := Sum.elim (fun i => (p i : ℝ)) (fun i => (p i : ℝ))

lemma sptSeq_eq : sptSeq x = (List.finRange k).flatMap (pr x) := by
  unfold sptSeq pr; rfl

lemma sum_flatMap (L : List (Fin k)) :
    (((L.flatMap (pr x))).map (tt p)).sum = (L.map (fun i => 2 * (p i : ℝ))).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons,
      List.sum_cons]
    unfold pr
    split_ifs <;> simp [tt] <;> ring

lemma mem_take (j i : Fin k) : i ∈ (List.finRange k).take j.val ↔ i.val < j.val := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨n, hn, h⟩
    rw [List.getElem_take, List.getElem_finRange] at h
    have : n < j.val := by simpa using hn
    have h2 : n = i.val := by
      have := congrArg Fin.val h
      simpa using this
    omega
  · intro h
    refine ⟨i.val, by simp; omega, ?_⟩
    rw [List.getElem_take, List.getElem_finRange]
    ext; simp

lemma sum_take (j : Fin k) :
    (((List.finRange k).take j.val).map (fun i => 2 * (p i : ℝ))).sum =
      2 * ∑ i ∈ Finset.univ.filter (fun i : Fin k => i < j), (p i : ℝ) := by
  have hnd : ((List.finRange k).take j.val).Nodup :=
    (List.nodup_finRange k).sublist (List.take_sublist _ _)
  rw [← List.sum_toFinset _ hnd]
  have : ((List.finRange k).take j.val).toFinset = Finset.univ.filter (fun i : Fin k => i < j) := by
    ext i; rw [List.mem_toFinset, mem_take, Finset.mem_filter]; simp
  rw [this, ← Finset.mul_sum]

lemma split (j : Fin k) :
    sptSeq x = ((List.finRange k).take j.val).flatMap (pr x) ++
      (pr x j ++ ((List.finRange k).drop (j.val + 1)).flatMap (pr x)) := by
  rw [sptSeq_eq]
  have h1 : j.val < (List.finRange k).length := by simp
  conv_lhs => rw [← List.take_append_drop j.val (List.finRange k)]
  rw [List.flatMap_append, List.drop_eq_getElem_cons h1, List.flatMap_cons, List.getElem_finRange]
  rfl

lemma ctA (j : Fin k) :
    completionTime (tt p) (sptSeq x) (Sum.inl j) =
      2 * ∑ i ∈ Finset.univ.filter (fun i : Fin k => i < j), (p i : ℝ) + p j +
        (if x j then (p j : ℝ) else 0) := by
  rw [split x j]
  have hn : (Sum.inl j : Fin k ⊕ Fin k) ∉ ((List.finRange k).take j.val).flatMap (pr x) := by
    intro h
    rw [List.mem_flatMap] at h
    obtain ⟨i, hi, hh⟩ := h
    rw [mem_take] at hi
    unfold pr at hh
    split_ifs at hh <;> simp at hh <;> subst hh <;> simp at hi
  rw [ttt_ct_append_right _ _ _ _ hn, sum_flatMap, sum_take]
  have hm : (Sum.inl j : Fin k ⊕ Fin k) ∈ pr x j := by unfold pr; split_ifs <;> simp
  rw [ttt_ct_append_left _ _ _ _ hm]
  unfold pr
  split_ifs with hx
  · simp [completionTime, completionAt, tt]; ring
  · simp [completionTime, completionAt, tt]

lemma ctB (j : Fin k) :
    completionTime (tt p) (sptSeq x) (Sum.inr j) =
      2 * ∑ i ∈ Finset.univ.filter (fun i : Fin k => i < j), (p i : ℝ) + p j +
        (if x j then 0 else (p j : ℝ)) := by
  rw [split x j]
  have hn : (Sum.inr j : Fin k ⊕ Fin k) ∉ ((List.finRange k).take j.val).flatMap (pr x) := by
    intro h
    rw [List.mem_flatMap] at h
    obtain ⟨i, hi, hh⟩ := h
    rw [mem_take] at hi
    unfold pr at hh
    split_ifs at hh <;> simp at hh <;> subst hh <;> simp at hi
  rw [ttt_ct_append_right _ _ _ _ hn, sum_flatMap, sum_take]
  have hm : (Sum.inr j : Fin k ⊕ Fin k) ∈ pr x j := by unfold pr; split_ifs <;> simp
  rw [ttt_ct_append_left _ _ _ _ hm]
  unfold pr
  split_ifs with hx
  · simp [completionTime, completionAt, tt]
  · simp [completionTime, completionAt, tt]; ring

lemma double_sum :
    ∑ j : Fin k, ∑ i ∈ Finset.univ.filter (fun i : Fin k => i < j), (p i : ℝ) =
      (weightedSum p : ℝ) := by
  have h1 : ∀ j : Fin k, ∑ i ∈ Finset.univ.filter (fun i : Fin k => i < j), (p i : ℝ) =
      ∑ i : Fin k, if i < j then (p i : ℝ) else 0 := by
    intro j; rw [Finset.sum_filter]
  simp_rw [h1]
  rw [Finset.sum_comm]
  unfold weightedSum
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter (fun j : Fin k => i < j)).card = k - (i.val + 1) := by
    have : Finset.univ.filter (fun j : Fin k => i < j) = Finset.Ioi i := by ext; simp
    rw [this, Fin.card_Ioi]; omega
  rw [hc]

end TTT

open TTT in
theorem solution {k : ℕ} (p : Fin k → ℕ) (hp : Monotone p) (x : Fin k → Bool) :
    (construction p).sumCA (sptSeq x) =
        (bigP p : ℝ) + 2 * (weightedSum p : ℝ) + (xSum p x : ℝ) ∧
      (construction p).sumCB (sptSeq x) =
        (bigP p : ℝ) + 2 * (weightedSum p : ℝ) + ((bigP p : ℝ) - (xSum p x : ℝ)) := by
  have hp' : (construction p).p = tt p := rfl
  have hA : (construction p).sumCA (sptSeq x) =
      ∑ j : Fin k, (2 * ∑ i ∈ Finset.univ.filter (fun i : Fin k => i < j), (p i : ℝ) + p j +
        (if x j then (p j : ℝ) else 0)) := by
    unfold Instance.sumCA Instance.C
    rw [hp']
    exact Finset.sum_congr rfl (fun j _ => ctA p x j)
  have hB : (construction p).sumCB (sptSeq x) =
      ∑ j : Fin k, (2 * ∑ i ∈ Finset.univ.filter (fun i : Fin k => i < j), (p i : ℝ) + p j +
        (if x j then 0 else (p j : ℝ))) := by
    unfold Instance.sumCB Instance.C
    rw [hp']
    exact Finset.sum_congr rfl (fun j _ => ctB p x j)
  have hx : (xSum p x : ℝ) = ∑ j : Fin k, (if x j then (p j : ℝ) else 0) := by
    unfold xSum; push_cast; simp [Nat.cast_ite]
  have hP : (bigP p : ℝ) = ∑ j : Fin k, (p j : ℝ) := by unfold bigP; push_cast; rfl
  have hD := double_sum p
  have hsplit : ∀ j : Fin k, (if x j then (0 : ℝ) else (p j : ℝ)) =
      (p j : ℝ) - (if x j then (p j : ℝ) else 0) := by
    intro j; split_ifs <;> simp
  constructor
  · rw [hA, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hD, ← hx, ← hP]
    ring
  · rw [hB, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hD]
    simp_rw [hsplit]
    rw [Finset.sum_sub_distrib, ← hx, ← hP]
    ring
