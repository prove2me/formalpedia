-- Prove2me | solution 1 for WorstCaseEq.Identical.nash_support_minimizes
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:28:57.881027+00:00
-- url     : https://prove2.me/submissions/296fb91a-013e-4814-b735-fa36476b68da

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

lemma lin (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ) (hp : AGT.IsMixedProfile (S := fun _ : Fin n => Fin m) p)
    (i : Fin n) (τ : Fin m → ℝ) (hτ : AGT.IsLottery τ) :
    -AGT.expectedPayoff (S := fun _ : Fin n => Fin m) (payoff w) (Function.update p i τ) i
      = ∑ a, τ a * linkCost w p i a := by
  classical
  have hq : AGT.IsMixedProfile (S := fun _ : Fin n => Fin m) (Function.update p i τ) := by
    intro l
    by_cases hl : l = i
    · subst hl; simpa using hτ
    · simp only [Function.update_of_ne hl]; exact hp l
  have h1 := expc w (Function.update p i τ) hq i
  have h2 : expCost w (Function.update p i τ) i
        = -AGT.expectedPayoff (S := fun _ : Fin n => Fin m) (payoff w) (Function.update p i τ) i := rfl
  rw [← h2, h1]
  unfold linkCost
  have e1 : ∑ a, τ a * (w i + ∑ k ∈ Finset.univ.erase i, p k a * w k)
      = w i + ∑ k ∈ Finset.univ.erase i, ∑ a, τ a * (p k a * w k) := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hτ.2, one_mul]
    congr 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [e1]
  congr 1
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hki : k ≠ i := Finset.ne_of_mem_erase hk
  unfold collisionProb
  simp only [Function.update_self, Function.update_of_ne hki, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => by ring)

end HHW

theorem solution {n m : ℕ} [NeZero m] (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ)
    (hp : IsNash w p) :
    (∀ i j, 0 < p i j → ∀ j', linkCost w p i j ≤ linkCost w p i j') ∧
      ∀ i, expCost w p i = Finset.univ.inf' Finset.univ_nonempty (linkCost w p i) := by
  classical
  have hmp : AGT.IsMixedProfile (S := fun _ : Fin n => Fin m) p := hp.1
  have hcost : ∀ i, expCost w p i = ∑ a, p i a * linkCost w p i a := by
    intro i
    have := HHW.lin w p hmp i (p i) (hmp i)
    rw [Function.update_eq_self] at this
    exact this
  have hle : ∀ i j', ∑ a, p i a * linkCost w p i a ≤ linkCost w p i j' := by
    intro i j'
    have hτ : AGT.IsLottery (pureLottery (m := m) j') := by
      refine ⟨fun a => ?_, ?_⟩
      · unfold pureLottery; split_ifs <;> norm_num
      · simp [pureLottery]
    have h1 := hp.2 i _ hτ
    have h2 := HHW.lin w p hmp i _ hτ
    have h3 : -AGT.expectedPayoff (S := fun _ : Fin n => Fin m) (payoff w) p i
        = ∑ a, p i a * linkCost w p i a := hcost i
    have h4 : ∑ a, pureLottery (m := m) j' a * linkCost w p i a = linkCost w p i j' := by
      simp [pureLottery]
    linarith
  have hmin : ∀ i, ∑ a, p i a * linkCost w p i a = Finset.univ.inf' Finset.univ_nonempty (linkCost w p i) := by
    intro i
    apply le_antisymm
    · exact Finset.le_inf' _ _ (fun j' _ => hle i j')
    · obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin m)) (linkCost w p i)
      calc Finset.univ.inf' Finset.univ_nonempty (linkCost w p i)
          = ∑ a, p i a * Finset.univ.inf' Finset.univ_nonempty (linkCost w p i) := by
            rw [← Finset.sum_mul, (hmp i).2, one_mul]
        _ ≤ ∑ a, p i a * linkCost w p i a := by
            refine Finset.sum_le_sum (fun a _ => ?_)
            exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ (Finset.mem_univ a)) ((hmp i).1 a)
  refine ⟨?_, fun i => (hcost i).trans (hmin i)⟩
  intro i j hj j'
  set E := ∑ a, p i a * linkCost w p i a with hE
  have hz : ∑ a, p i a * (linkCost w p i a - E) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, (hmp i).2, one_mul]
    rw [← hE]; ring
  have hnn : ∀ a ∈ Finset.univ, 0 ≤ p i a * (linkCost w p i a - E) := by
    intro a _
    exact mul_nonneg ((hmp i).1 a) (sub_nonneg.mpr (hle i a))
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz j (Finset.mem_univ j)
  have h5 : linkCost w p i j - E = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hj.ne'
    · exact h
  have := hle i j'
  linarith
