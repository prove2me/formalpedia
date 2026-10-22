-- Prove2me | solution 1 for WorstCaseEq.Identical.theorem2_expected_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:43:26.951367+00:00
-- url     : https://prove2.me/submissions/b9eb9c65-a30f-4450-9e50-839a706a87f1

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

lemma nash_facts {n m : ℕ} (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ) (hp : IsNash w p) :
    (∀ i, expCost w p i = ∑ a, p i a * linkCost w p i a) ∧
    (∀ i j', ∑ a, p i a * linkCost w p i a ≤ linkCost w p i j') := by
  classical
  have hmp : AGT.IsMixedProfile (S := fun _ : Fin n => Fin m) p := hp.1
  have hcost : ∀ i, expCost w p i = ∑ a, p i a * linkCost w p i a := by
    intro i
    have := lin w p hmp i (p i) (hmp i)
    rw [Function.update_eq_self] at this
    exact this
  refine ⟨hcost, ?_⟩
  intro i j'
  have hτ : AGT.IsLottery (pureLottery (m := m) j') := by
    refine ⟨fun a => ?_, ?_⟩
    · unfold pureLottery; split_ifs <;> norm_num
    · simp [pureLottery]
  have h1 := hp.2 i _ hτ
  have h2 := lin w p hmp i _ hτ
  have h3 : -AGT.expectedPayoff (S := fun _ : Fin n => Fin m) (payoff w) p i
      = ∑ a, p i a * linkCost w p i a := hcost i
  have h4 : ∑ a, pureLottery (m := m) j' a * linkCost w p i a = linkCost w p i j' := by
    simp [pureLottery]
  linarith

lemma sum_link_cost {n m : ℕ} (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ)
    (hp : AGT.IsMixedProfile (S := fun _ : Fin n => Fin m) p) (i : Fin n) :
    ∑ j, linkCost w p i j = (m : ℝ) * w i + (∑ k, w k - w i) := by
  unfold linkCost
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  rw [Finset.sum_comm]
  have : ∀ k ∈ Finset.univ.erase i, ∑ j, p k j * w k = w k := by
    intro k _
    rw [← Finset.sum_mul, (hp k).2, one_mul]
  rw [Finset.sum_congr rfl this]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  ring

lemma load_ge {n m : ℕ} [NeZero m] (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (s : Fin n → Fin m) (i : Fin n) :
    w i ≤ makespan w s := by
  have h1 : w i ≤ load w s (s i) := by
    unfold load
    exact Finset.single_le_sum (f := w) (fun k _ => (hw k).le) (by simp)
  exact le_trans h1 (Finset.le_sup' (load w s) (Finset.mem_univ (s i)))

lemma sum_le_makespan {n m : ℕ} [NeZero m] (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (s : Fin n → Fin m) :
    ∑ k, w k ≤ (m : ℝ) * makespan w s := by
  have h1 : ∑ k, w k = ∑ j, load w s j := by
    unfold load
    rw [Finset.sum_fiberwise]
  rw [h1]
  calc ∑ j, load w s j ≤ ∑ j : Fin m, makespan w s :=
        Finset.sum_le_sum (fun j _ => Finset.le_sup' (load w s) (Finset.mem_univ j))
    _ = (m : ℝ) * makespan w s := by simp

end HHW

theorem solution {n m : ℕ} [NeZero m] (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (p : Fin n → Fin m → ℝ) (hp : IsNash w p) :
    ∀ i, expCost w p i ≤ (∑ k, w k) / m + (((m : ℝ) - 1) / m) * w i ∧
      expCost w p i ≤ (2 - 1 / (m : ℝ)) * opt m w := by
  intro i
  have hmp : AGT.IsMixedProfile (S := fun _ : Fin n => Fin m) p := hp.1
  obtain ⟨hcost, hle⟩ := HHW.nash_facts w p hp
  have hmpos : (0 : ℝ) < m := by
    have := Nat.pos_of_ne_zero (NeZero.ne m)
    exact_mod_cast this
  have hE : expCost w p i ≤ ((m : ℝ) * w i + (∑ k, w k - w i)) / m := by
    rw [le_div_iff₀ hmpos]
    have h1 : ∑ j : Fin m, expCost w p i ≤ ∑ j, linkCost w p i j :=
      Finset.sum_le_sum (fun j _ => by rw [hcost i]; exact hle i j)
    rw [HHW.sum_link_cost w p hmp i] at h1
    simp at h1
    linarith
  have h6 : expCost w p i ≤ (∑ k, w k) / m + (((m : ℝ) - 1) / m) * w i := by
    refine le_trans hE (le_of_eq ?_)
    field_simp
    ring
  refine ⟨h6, ?_⟩
  have hopt1 : w i ≤ opt m w := Finset.le_inf' _ _ (fun s _ => HHW.load_ge w hw s i)
  have hopt2 : (∑ k, w k) / m ≤ opt m w := by
    refine Finset.le_inf' _ _ (fun s _ => ?_)
    rw [div_le_iff₀ hmpos, mul_comm]
    exact HHW.sum_le_makespan w hw s
  have hm1 : (1 : ℝ) ≤ m := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hc : 0 ≤ ((m : ℝ) - 1) / m := div_nonneg (by linarith) hmpos.le
  calc expCost w p i ≤ (∑ k, w k) / m + (((m : ℝ) - 1) / m) * w i := h6
    _ ≤ opt m w + (((m : ℝ) - 1) / m) * opt m w :=
        add_le_add hopt2 (mul_le_mul_of_nonneg_left hopt1 hc)
    _ = (2 - 1 / (m : ℝ)) * opt m w := by
        field_simp
        ring
