-- Prove2me | solution 1 for WorstCaseEq.Identical.eq7_contrib_add_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:26:09.488271+00:00
-- url     : https://prove2.me/submissions/7ae5b4f9-189c-4a78-a51f-f101dca370a7

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Identical_Model

set_option autoImplicit false
open WorstCaseEq.Identical

namespace HHW
variable {n m : ℕ}

lemma key (p : Fin n → Fin m → ℝ) (hp : AGT.IsMixedProfile (S := fun _ : Fin n => Fin m) p)
    (T : Finset (Fin n)) (G : Fin n → Fin m → ℝ) :
    ∑ s : Fin n → Fin m, (∏ l, p l (s l)) * ∏ l ∈ T, G l (s l) = ∏ l ∈ T, ∑ a, p l a * G l a := by
  classical
  have h1 : ∀ s : Fin n → Fin m, (∏ l, p l (s l)) * ∏ l ∈ T, G l (s l)
      = ∏ l, (p l (s l) * (if l ∈ T then G l (s l) else 1)) := by
    intro s
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]
  simp_rw [h1]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum
    (fun l => (Finset.univ : Finset (Fin m))) (fun l a => p l a * (if l ∈ T then G l a else 1))]
  have h2 : ∀ l : Fin n, ∑ a, p l a * (if l ∈ T then G l a else 1)
      = if l ∈ T then ∑ a, p l a * G l a else 1 := by
    intro l
    by_cases hl : l ∈ T
    · simp [hl]
    · simp [hl, (hp l).2]
  simp_rw [h2]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

lemma sum_prob (p : Fin n → Fin m → ℝ) (hp : AGT.IsMixedProfile (S := fun _ : Fin n => Fin m) p) :
    ∑ s : Fin n → Fin m, ∏ l, p l (s l) = 1 := by
  have := key p hp ∅ (fun _ _ => 1)
  simpa using this

lemma coll (p : Fin n → Fin m → ℝ) (hp : AGT.IsMixedProfile (S := fun _ : Fin n => Fin m) p)
    (i k : Fin n) (hik : i ≠ k) :
    ∑ s : Fin n → Fin m, (∏ l, p l (s l)) * (if s i = s k then (1:ℝ) else 0)
      = collisionProb p i k := by
  classical
  have h1 : ∀ s : Fin n → Fin m, (if s i = s k then (1:ℝ) else 0)
      = ∑ j : Fin m, ∏ l ∈ ({i, k} : Finset (Fin n)), (if s l = j then (1:ℝ) else 0) := by
    intro s
    simp only [Finset.prod_pair hik]
    by_cases h : s i = s k
    · simp [h]
    · rw [if_neg h]
      symm
      apply Finset.sum_eq_zero
      intro j _
      by_cases a : s i = j
      · have : s k ≠ j := fun b => h (a.trans b.symm)
        simp [this]
      · simp [a]
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ j : Fin m, ∑ s : Fin n → Fin m, (∏ l, p l (s l)) *
      ∏ l ∈ ({i, k} : Finset (Fin n)), (if s l = j then (1:ℝ) else 0) = p i j * p k j := by
    intro j
    rw [key p hp {i, k} (fun _ a => if a = j then (1:ℝ) else 0)]
    simp [Finset.prod_pair hik]
  simp_rw [h2]
  rfl


lemma expc {n m : ℕ} (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ)
    (hp : AGT.IsMixedProfile (S := fun _ : Fin n => Fin m) p) :
    ∀ i, expCost w p i = w i + ∑ k ∈ Finset.univ.erase i, collisionProb p i k * w k := by
  classical
  intro i
  have h1 : expCost w p i = ∑ s : Fin n → Fin m, (∏ l, p l (s l)) *
      ∑ k, (if s i = s k then w k else 0) := by
    unfold expCost AGT.expectedPayoff AGT.profileProb payoff load
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.sum_filter]
    simp only [mul_neg, neg_neg]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [eq_comm]
  have h2 : ∀ s : Fin n → Fin m, (∏ l, p l (s l)) * ∑ k, (if s i = s k then w k else 0)
      = ∑ k, w k * ((∏ l, p l (s l)) * (if s i = s k then (1:ℝ) else 0)) := by
    intro s
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    split_ifs <;> ring
  rw [h1]
  simp_rw [h2]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  · simp [sum_prob p hp]
  · refine Finset.sum_congr rfl (fun k hk => ?_)
    have hki : i ≠ k := fun h => (Finset.ne_of_mem_erase hk) h.symm
    rw [coll p hp i k hki]
    ring

lemma fm_unique [NeZero m] (w : Fin n → ℝ) (s : Fin n → Fin m) (j j' : Fin m)
    (h : IsFirstMaxLink w s j) (h' : IsFirstMaxLink w s j') : j = j' := by
  rcases lt_trichotomy j j' with hl | he | hg
  · exact absurd h.1 (ne_of_lt (h'.2 j hl))
  · exact he
  · exact absurd h'.1 (ne_of_lt (h.2 j' hg))

lemma fm_exists [NeZero m] (w : Fin n → ℝ) (s : Fin n → Fin m) :
    ∃ j, IsFirstMaxLink w s j := by
  classical
  obtain ⟨j0, -, hmax⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin m)) (load w s)
  let A := Finset.univ.filter (fun j => load w s j = makespan w s)
  have hA : A.Nonempty := ⟨j0, by simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]; unfold makespan; exact hmax.symm⟩
  refine ⟨A.min' hA, ?_, ?_⟩
  · have := A.min'_mem hA
    simpa [A] using this
  · intro j' hj'
    have hle : load w s j' ≤ makespan w s := Finset.le_sup' (load w s) (Finset.mem_univ j')
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      have : A.min' hA ≤ j' := Finset.min'_le A j' (by simp [A, h])
      exact absurd hj' (not_lt.mpr this)

open Classical in
lemma ms_eq [NeZero m] (w : Fin n → ℝ) (s : Fin n → Fin m) :
    makespan w s = ∑ i, (if IsFirstMaxLink w s (s i) then (1:ℝ) else 0) * w i := by
  obtain ⟨j0, hj0⟩ := fm_exists w s
  have h1 : ∀ i, (if IsFirstMaxLink w s (s i) then (1:ℝ) else 0) * w i
      = if s i = j0 then w i else 0 := by
    intro i
    by_cases h : s i = j0
    · subst h; simp [hj0]
    · have : ¬ IsFirstMaxLink w s (s i) := fun hh => h (fm_unique w s _ _ hh hj0)
      simp [this, h]
  simp_rw [h1]
  rw [← Finset.sum_filter]
  exact hj0.1.symm

lemma prob_nonneg (p : Fin n → Fin m → ℝ) (hp : AGT.IsMixedProfile (S := fun _ : Fin n => Fin m) p)
    (s : Fin n → Fin m) : 0 ≤ ∏ l, p l (s l) :=
  Finset.prod_nonneg (fun l _ => (hp l).1 _)

end HHW

open Classical in
theorem solution {n m : ℕ} [NeZero m] (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ)
    (hp : AGT.IsMixedProfile (S := fun _ : Fin n => Fin m) p) :
    ∀ i k, i ≠ k → contribProb w p i + contribProb w p k ≤ 1 + collisionProb p i k := by
  intro i k hik
  have hc := HHW.coll p hp i k hik
  have h1 := HHW.sum_prob p hp
  unfold contribProb
  rw [← hc, ← Finset.sum_add_distrib]
  refine le_trans (Finset.sum_le_sum (g := fun s : Fin n → Fin m => (∏ l, p l (s l)) +
    (∏ l, p l (s l)) * (if s i = s k then (1:ℝ) else 0)) ?_) (le_of_eq ?_)
  · intro s _
    have h0 : 0 ≤ AGT.profileProb (S := fun _ : Fin n => Fin m) p s := HHW.prob_nonneg p hp s
    have hle : (if IsFirstMaxLink w s (s i) then (1:ℝ) else 0) + (if IsFirstMaxLink w s (s k) then (1:ℝ) else 0)
        ≤ 1 + (if s i = s k then (1:ℝ) else 0) := by
      by_cases a : IsFirstMaxLink w s (s i) <;> by_cases b : IsFirstMaxLink w s (s k)
      · have : s i = s k := HHW.fm_unique w s _ _ a b
        simp [a, b, this]
      · simp [a, b]; split_ifs <;> norm_num
      · simp [a, b]; split_ifs <;> norm_num
      · simp [a, b]; split_ifs <;> norm_num
    have key := mul_le_mul_of_nonneg_left hle h0
    simp only [AGT.profileProb] at key h0 ⊢
    linarith
  · rw [Finset.sum_add_distrib, h1]
