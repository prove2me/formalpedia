-- Prove2me | solution 1 for SchedComplexity.NoWait.theorem_5b_equiv
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:59:47.939315+00:00
-- url     : https://prove2.me/submissions/9e98e3d6-81d7-4448-9e5f-5f6ef22f328f

import Mathlib
import Definitions.Def_SchedComplexity_NoWait_DirectedGraphs
import Definitions.Def_SchedComplexity_NoWait_Construction



namespace SchedComplexity.NoWait

section cons
variable {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ) (lam mu : ℕ)

theorem ps_bd (ℓ : Fin n) (i : ℕ) :
    (i : ℤ) * mu - lam - 1 ≤ partialSum adj ι lam mu ℓ i ∧
      partialSum adj ι lam mu ℓ i ≤ (i : ℤ) * mu + lam + 1 := by
  have : (0:ℤ) ≤ lam := by positivity
  unfold partialSum
  split_ifs <;> constructor <;> linarith

theorem procTimes_pos_core (hι : Admissible n ι) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu)
    (ℓ : Fin n) (r : Fin (numMachines n)) : 1 ≤ procTimeInt adj ι lam mu ℓ r := by
  have h1 : (1:ℤ) ≤ lam := by exact_mod_cast hlam
  have h2 : (2:ℤ) * lam + 3 ≤ mu := by exact_mod_cast hmu
  unfold procTimeInt
  split_ifs with h
  · have := (ps_bd adj ι lam mu ℓ 1).1
    push_cast at this
    linarith
  · have a := (ps_bd adj ι lam mu ℓ (r.val+1)).1
    have b := (ps_bd adj ι lam mu ℓ r.val).2
    push_cast at a b
    linarith


theorem cum_succ' {m : ℕ} (p : Fin n → Fin m → ℕ) (ℓ : Fin n) (i : ℕ) (h : i < m) :
    cum p ℓ (i+1) = cum p ℓ i + p ℓ ⟨i, h⟩ := by
  unfold cum
  have : Finset.univ.filter (fun r : Fin m => r.val < i + 1) =
      insert ⟨i, h⟩ (Finset.univ.filter (fun r : Fin m => r.val < i)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [this, Finset.sum_insert (by simp), add_comm]

theorem ps_zero (hι : Admissible n ι) (ℓ : Fin n) : partialSum adj ι lam mu ℓ 0 = 0 := by
  have h1 : ¬ ∃ k : Fin n, k ≠ ℓ ∧ 0 = ι ℓ k ∧ adj ℓ k = true := by
    rintro ⟨k, hk, h, _⟩
    have := (hι.1 ℓ k hk.symm).1
    omega
  have h2 : ¬ ∃ k : Fin n, k ≠ ℓ ∧ 0 = ι ℓ k ∧ adj ℓ k = false := by
    rintro ⟨k, hk, h, _⟩
    have := (hι.1 ℓ k hk.symm).1
    omega
  have h3 : ¬ ∃ j : Fin n, j ≠ ℓ ∧ 0 + 1 = ι j ℓ ∧ adj j ℓ = true := by
    rintro ⟨k, hk, h, _⟩
    have := (hι.1 k ℓ hk).1
    omega
  have h4 : ¬ ∃ j : Fin n, j ≠ ℓ ∧ 0 + 1 = ι j ℓ ∧ adj j ℓ = false := by
    rintro ⟨k, hk, h, _⟩
    have := (hι.1 k ℓ hk).1
    omega
  unfold partialSum
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  simp

theorem ps_pos_arc (hι : Admissible n ι) (j k : Fin n) (hjk : j ≠ k) (i : ℕ) (hi : i = ι j k)
    (ha : adj j k = true) : partialSum adj ι lam mu j i = (i : ℤ) * mu + lam := by
  unfold partialSum
  rw [if_pos ⟨k, hjk.symm, hi, ha⟩]

theorem ps_pos_noarc (hι : Admissible n ι) (j k : Fin n) (hjk : j ≠ k) (i : ℕ) (hi : i = ι j k)
    (ha : adj j k = false) : partialSum adj ι lam mu j i = (i : ℤ) * mu + lam + 1 := by
  have h1 : ¬ ∃ k' : Fin n, k' ≠ j ∧ i = ι j k' ∧ adj j k' = true := by
    rintro ⟨k', hk', h, hh⟩
    have := hι.2.1 j k j k' hjk hk'.symm (by omega)
    have : k = k' := this.2
    subst this
    rw [ha] at hh; exact Bool.false_ne_true hh
  unfold partialSum
  rw [if_neg h1, if_pos ⟨k, hjk.symm, hi, ha⟩]

theorem ps_neg_arc (hι : Admissible n ι) (j k : Fin n) (hjk : j ≠ k) (i : ℕ) (hi : i + 1 = ι j k)
    (ha : adj j k = true) : partialSum adj ι lam mu k i = (i : ℤ) * mu - lam := by
  have h1 : ¬ ∃ k' : Fin n, k' ≠ k ∧ i = ι k k' ∧ adj k k' = true := by
    rintro ⟨k', hk', h, _⟩
    exact hι.2.2.2 j k k' hjk hk'.symm (by omega)
  have h2 : ¬ ∃ k' : Fin n, k' ≠ k ∧ i = ι k k' ∧ adj k k' = false := by
    rintro ⟨k', hk', h, _⟩
    exact hι.2.2.2 j k k' hjk hk'.symm (by omega)
  unfold partialSum
  rw [if_neg h1, if_neg h2, if_pos ⟨j, hjk, hi, ha⟩]

theorem ps_neg_noarc (hι : Admissible n ι) (j k : Fin n) (hjk : j ≠ k) (i : ℕ) (hi : i + 1 = ι j k)
    (ha : adj j k = false) : partialSum adj ι lam mu k i = (i : ℤ) * mu - lam - 1 := by
  have h1 : ¬ ∃ k' : Fin n, k' ≠ k ∧ i = ι k k' ∧ adj k k' = true := by
    rintro ⟨k', hk', h, _⟩
    exact hι.2.2.2 j k k' hjk hk'.symm (by omega)
  have h2 : ¬ ∃ k' : Fin n, k' ≠ k ∧ i = ι k k' ∧ adj k k' = false := by
    rintro ⟨k', hk', h, _⟩
    exact hι.2.2.2 j k k' hjk hk'.symm (by omega)
  have h3 : ¬ ∃ j' : Fin n, j' ≠ k ∧ i + 1 = ι j' k ∧ adj j' k = true := by
    rintro ⟨j', hj', h, hh⟩
    have := hι.2.1 j k j' k hjk hj'.symm.symm.symm.symm (by omega)
    have : j = j' := this.1
    subst this
    rw [ha] at hh; exact Bool.false_ne_true hh
  unfold partialSum
  rw [if_neg h1, if_neg h2, if_neg h3, if_pos ⟨j, hjk, hi, ha⟩]

theorem ps_le_of_not_pos (ℓ : Fin n) (i : ℕ) (hlam : 1 ≤ lam)
    (h : ¬ ∃ k : Fin n, k ≠ ℓ ∧ i = ι ℓ k) : partialSum adj ι lam mu ℓ i ≤ (i : ℤ) * mu := by
  have : (0:ℤ) ≤ lam := by positivity
  unfold partialSum
  split_ifs with a b c d
  · exact absurd (by obtain ⟨k, hk, h1, _⟩ := a; exact ⟨k, hk, h1⟩) h
  · exact absurd (by obtain ⟨k, hk, h1, _⟩ := b; exact ⟨k, hk, h1⟩) h
  · linarith
  · linarith
  · exact le_refl _

theorem ps_ge_of_not_neg (ℓ : Fin n) (i : ℕ) (hlam : 1 ≤ lam)
    (h : ¬ ∃ j : Fin n, j ≠ ℓ ∧ i + 1 = ι j ℓ) : (i : ℤ) * mu ≤ partialSum adj ι lam mu ℓ i := by
  have : (0:ℤ) ≤ lam := by positivity
  unfold partialSum
  split_ifs with a b c d
  · linarith
  · linarith
  · exact absurd (by obtain ⟨k, hk, h1, _⟩ := c; exact ⟨k, hk, h1⟩) h
  · exact absurd (by obtain ⟨k, hk, h1, _⟩ := d; exact ⟨k, hk, h1⟩) h
  · exact le_refl _

theorem cum_eq_ps (hι : Admissible n ι) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu) (ℓ : Fin n) :
    ∀ i : ℕ, i ≤ numMachines n →
      (cum (procTimes adj ι lam mu) ℓ i : ℤ) = partialSum adj ι lam mu ℓ i := by
  intro i
  induction i with
  | zero => intro _; rw [ps_zero adj ι lam mu hι]; simp [cum]
  | succ i ih =>
    intro hi
    have ih := ih (by omega)
    rw [cum_succ' (procTimes adj ι lam mu) ℓ i (by omega)]
    push_cast
    rw [ih]
    have hp := procTimes_pos_core adj ι lam mu hι hlam hmu ℓ ⟨i, by omega⟩
    have : (procTimes adj ι lam mu ℓ ⟨i, by omega⟩ : ℤ) = procTimeInt adj ι lam mu ℓ ⟨i, by omega⟩ := by
      unfold procTimes
      exact Int.toNat_of_nonneg (by omega)
    rw [this]
    unfold procTimeInt
    by_cases h0 : i = 0
    · subst h0
      simp [ps_zero adj ι lam mu hι]
    · simp only [Fin.val_mk, h0, if_false]
      ring


theorem delay_construction_core (hι : Admissible n ι) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu)
    (j k : Fin n) (hjk : j ≠ k) :
    delay (procTimes adj ι lam mu) (numMachines_pos n) j k =
      if adj j k = true then (mu : ℤ) + 2 * lam else (mu : ℤ) + 2 * lam + 2 := by
  have hl : (1:ℤ) ≤ lam := by exact_mod_cast hlam
  apply le_antisymm
  · unfold delay
    apply Finset.sup'_le
    intro r _
    have hr := r.isLt
    rw [cum_eq_ps adj ι lam mu hι hlam hmu j (r.val+1) (by omega),
      cum_eq_ps adj ι lam mu hι hlam hmu k r.val (by omega)]
    have b1 := (ps_bd adj ι lam mu j (r.val+1)).2
    have b2 := (ps_bd adj ι lam mu k r.val).1
    push_cast at b1 b2
    by_cases ha : adj j k = true
    · rw [if_pos ha]
      by_cases hP : ∃ k' : Fin n, k' ≠ j ∧ r.val + 1 = ι j k'
      · by_cases hN : ∃ j' : Fin n, j' ≠ k ∧ r.val + 1 = ι j' k
        · obtain ⟨k', hk', e1⟩ := hP
          obtain ⟨j', hj', e2⟩ := hN
          have := hι.2.1 j k' j' k hk'.symm hj' (by omega)
          obtain ⟨rfl, rfl⟩ := this
          rw [ps_pos_arc adj ι lam mu hι j k' hjk _ e1 ha,
            ps_neg_arc adj ι lam mu hι j k' hjk r.val e1 ha]
          push_cast
          linarith
        · have := ps_ge_of_not_neg adj ι lam mu k r.val hlam hN
          linarith
      · have := ps_le_of_not_pos adj ι lam mu j (r.val+1) hlam hP
        push_cast at this
        linarith
    · rw [if_neg ha]
      linarith
  · obtain ⟨r0, hr0⟩ : ∃ r0, ι j k = r0 + 1 := ⟨ι j k - 1, by have := (hι.1 j k hjk).1; omega⟩
    have hb := (hι.1 j k hjk).2
    have hr : r0 < numMachines n := by unfold numMachines; omega
    refine le_trans ?_ (Finset.le_sup' (fun r : Fin (numMachines n) =>
      (cum (procTimes adj ι lam mu) j (r.val + 1) : ℤ) - (cum (procTimes adj ι lam mu) k r.val : ℤ))
      (Finset.mem_univ (⟨r0, hr⟩ : Fin (numMachines n))))
    simp only [Fin.val_mk]
    rw [cum_eq_ps adj ι lam mu hι hlam hmu j (r0+1) (by omega),
      cum_eq_ps adj ι lam mu hι hlam hmu k r0 (by omega)]
    by_cases ha : adj j k = true
    · rw [if_pos ha, ps_pos_arc adj ι lam mu hι j k hjk (r0+1) hr0.symm ha,
        ps_neg_arc adj ι lam mu hι j k hjk r0 hr0.symm ha]
      push_cast; linarith
    · have ha' : adj j k = false := by simpa using ha
      rw [if_neg ha, ps_pos_noarc adj ι lam mu hι j k hjk (r0+1) hr0.symm ha',
        ps_neg_noarc adj ι lam mu hι j k hjk r0 hr0.symm ha']
      push_cast; linarith

end cons


section tsp
variable {n m : ℕ} (p : Fin n → Fin m → ℕ)

theorem tsp_cum_zero (l : Fin n) : cum p l 0 = 0 := by simp [cum]

theorem tsp_cum_mono (l : Fin n) (r : ℕ) : cum p l r ≤ cum p l (r + 1) := by
  unfold cum
  apply Finset.sum_le_sum_of_subset
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  omega

theorem tsp_cum_strict (hp : ∀ ℓ r, 0 < p ℓ r) (l : Fin n) (r : ℕ) (hr : r < m) :
    cum p l r < cum p l (r + 1) := by
  unfold cum
  refine Finset.sum_lt_sum_of_subset (i := ⟨r, hr⟩) ?_ ?_ ?_ (hp _ _) (fun _ _ _ => Nat.zero_le _)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    omega
  · simp
  · simp

theorem tsp_cum_end (hm : 0 < m) (l : Fin n) : cum p l (m - 1 + 1) = cum p l m := by
  congr 1; omega

theorem tsp_c_nonneg (hm : 0 < m) (j k : Fin n) : 0 ≤ delay p hm j k := by
  have h := Finset.le_sup' (fun r : Fin m => (cum p j (r.val + 1) : ℤ) - (cum p k r.val : ℤ))
    (Finset.mem_univ (⟨0, hm⟩ : Fin m))
  have h2 : (0:ℤ) ≤ (cum p j (0 + 1) : ℤ) - (cum p k 0 : ℤ) := by
    simp [cum]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  exact le_trans h2 h

theorem tsp_c_ge (hm : 0 < m) (j k : Fin n) (r : Fin m) :
    (cum p j (r.val + 1) : ℤ) ≤ delay p hm j k + (cum p k r.val : ℤ) := by
  have h := Finset.le_sup' (fun r : Fin m => (cum p j (r.val + 1) : ℤ) - (cum p k r.val : ℤ))
    (Finset.mem_univ r)
  unfold delay
  linarith

theorem tsp_c_le (hm : 0 < m) (j k : Fin n) (δ : ℤ)
    (h : ∀ r : Fin m, (cum p j (r.val + 1) : ℤ) ≤ δ + (cum p k r.val : ℤ)) :
    delay p hm j k ≤ δ := by
  unfold delay
  apply Finset.sup'_le
  intro r _
  have := h r
  linarith

theorem tsp_tri (hm : 0 < m) (j l k : Fin n) :
    delay p hm j k ≤ delay p hm j l + delay p hm l k := by
  apply tsp_c_le
  intro r
  have h1 := tsp_c_ge p hm j l r
  have h2 := tsp_c_ge p hm l k r
  have h3 := tsp_cum_mono p l r.val
  have h3' : (cum p l r.val : ℤ) ≤ (cum p l (r.val+1) : ℤ) := by exact_mod_cast h3
  linarith

theorem tsp_end (hm : 0 < m) (j k : Fin n) :
    (cum p j m : ℤ) ≤ delay p hm j k + (cum p k m : ℤ) := by
  have h1 := tsp_c_ge p hm j k ⟨m - 1, by omega⟩
  have h2 := tsp_cum_mono p k (m - 1)
  have h2' : (cum p k (m-1) : ℤ) ≤ (cum p k (m-1+1) : ℤ) := by exact_mod_cast h2
  simp only at h1
  rw [tsp_cum_end p hm] at h1 h2'
  linarith

theorem tsp_disj_of_le {a b c d : ℕ} (h : b ≤ c) : Disjoint (Set.Ico a b) (Set.Ico c d) := by
  rw [Set.Ico_disjoint_Ico]; omega


end tsp

def Jf {N : ℕ} (π : Fin (N+1) ≃ Fin (N+1)) (k : ℕ) : Fin (N+1) := π ⟨min k N, by omega⟩

section seq
variable {N m : ℕ} (p : Fin (N+1) → Fin m → ℕ) (hm : 0 < m) (π : Fin (N+1) ≃ Fin (N+1))

def dd (k : ℕ) : ℤ := if k < N then delay p hm (Jf π k) (Jf π (k+1)) else 0

def SS (k : ℕ) : ℤ := ∑ i ∈ Finset.range k, dd p hm π i

theorem Jf_fin (i : Fin (N+1)) : Jf π i.val = π i := by
  unfold Jf
  have := i.isLt
  exact congrArg π (Fin.ext (by simp only; omega))

theorem dd_nonneg (k : ℕ) : 0 ≤ dd p hm π k := by
  unfold dd
  split_ifs
  · exact tsp_c_nonneg p hm _ _
  · exact le_refl _

theorem SS_nonneg (k : ℕ) : 0 ≤ SS p hm π k :=
  Finset.sum_nonneg (fun i _ => dd_nonneg p hm π i)

theorem SS_succ (k : ℕ) : SS p hm π (k+1) = SS p hm π k + dd p hm π k := by
  unfold SS; rw [Finset.sum_range_succ]

theorem pm_eq : pathMakespan p hm π = SS p hm π N + (cum p (π (Fin.last N)) m : ℤ) := by
  unfold pathMakespan
  have key : ∀ i : Fin (N+1), (if h : i.val + 1 < N + 1 then delay p hm (π i) (π ⟨i.val + 1, h⟩)
      else (cum p (π i) m : ℤ)) =
      (fun k : ℕ => if k < N then dd p hm π k else (cum p (Jf π k) m : ℤ)) i.val := by
    intro i
    have hi := i.isLt
    simp only [dd]
    by_cases h : i.val < N
    · have h' : i.val + 1 < N + 1 := by omega
      rw [dif_pos h', if_pos h, if_pos h, Jf_fin]
      congr 1
      unfold Jf
      exact congrArg π (Fin.ext (by simp only; omega))
    · have h' : ¬ i.val + 1 < N + 1 := by omega
      rw [dif_neg h', if_neg h, Jf_fin]
  rw [Finset.sum_congr rfl (fun i _ => key i),
    Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < N then dd p hm π k else (cum p (Jf π k) m : ℤ)) (N+1),
    Finset.sum_range_succ]
  have h1 : ∑ i ∈ Finset.range N, (if i < N then dd p hm π i else (cum p (Jf π i) m : ℤ))
      = SS p hm π N := by
    unfold SS
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (Finset.mem_range.mp hi)]
  rw [h1, if_neg (lt_irrefl N)]
  have : Jf π N = π (Fin.last N) := by
    have := Jf_fin π (Fin.last N)
    simpa using this
  rw [this]

theorem pt_eq : pathTotalCompletion p hm π =
    ∑ k : Fin (N+1), (SS p hm π k.val + (cum p (π k) m : ℤ)) := by
  unfold pathTotalCompletion
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  have key : ∀ i : Fin (N+1), (if h : i.val < k.val then
        delay p hm (π i) (π ⟨i.val + 1, by have := k.isLt; omega⟩) else 0) =
      (fun j : ℕ => if j < k.val then dd p hm π j else 0) i.val := by
    intro i
    have hk := k.isLt
    by_cases h : i.val < k.val
    · simp only [dd]
      rw [dif_pos h, if_pos h, if_pos (by omega), Jf_fin]
      congr 1
      unfold Jf
      exact congrArg π (Fin.ext (by simp only; omega))
    · simp [h]
  rw [Finset.sum_congr rfl (fun i _ => key i),
    Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < k.val then dd p hm π j else 0) (N+1),
    ← Finset.sum_filter]
  unfold SS
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  have := k.isLt
  simp only [Finset.mem_filter, Finset.mem_range]
  omega


theorem gap (a b : ℕ) (hab : a < b) (hb : b ≤ N) :
    delay p hm (Jf π a) (Jf π b) ≤ SS p hm π b - SS p hm π a := by
  induction b, hab using Nat.le_induction with
  | base =>
    rw [SS_succ]
    have : dd p hm π a = delay p hm (Jf π a) (Jf π (a+1)) := by
      unfold dd; rw [if_pos (by omega)]
    linarith
  | succ b hb1 ih =>
    have ih := ih (by omega)
    rw [SS_succ]
    have : dd p hm π b = delay p hm (Jf π b) (Jf π (b+1)) := by
      unfold dd; rw [if_pos (by omega)]
    have := tsp_tri p hm (Jf π a) (Jf π b) (Jf π (b+1))
    linarith

theorem build : ∃ B : Fin (N+1) → ℕ, IsNoWaitSchedule p B ∧
    ∀ k : Fin (N+1), (B (π k) : ℤ) = SS p hm π k.val := by
  refine ⟨fun ℓ => (SS p hm π (π.symm ℓ).val).toNat, ?_, ?_⟩
  · have hB : ∀ ℓ : Fin (N+1), ((SS p hm π (π.symm ℓ).val).toNat : ℤ) = SS p hm π (π.symm ℓ).val :=
      fun ℓ => Int.toNat_of_nonneg (SS_nonneg p hm π _)
    have main : ∀ j k : Fin (N+1), (π.symm j).val < (π.symm k).val → ∀ r : Fin m,
        (SS p hm π (π.symm j).val).toNat + cum p j (r.val + 1) ≤
          (SS p hm π (π.symm k).val).toNat + cum p k r.val := by
      intro j k hjk r
      have g := gap p hm π _ _ hjk (by have := (π.symm k).isLt; omega)
      rw [Jf_fin, Jf_fin] at g
      simp only [Equiv.apply_symm_apply] at g
      have c := tsp_c_ge p hm j k r
      have h1 := hB j
      have h2 := hB k
      zify
      linarith
    intro j k hjk r
    have hne : (π.symm j).val ≠ (π.symm k).val := by
      intro h
      exact hjk (by simpa using congrArg π (Fin.ext h))
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact tsp_disj_of_le (main j k h r)
    · exact (tsp_disj_of_le (main k j h r)).symm
  · intro k
    simp only [Equiv.symm_apply_apply]
    exact Int.toNat_of_nonneg (SS_nonneg p hm π _)

theorem GG_mono (k t : ℕ) (h : k + t ≤ N) :
    SS p hm π k + (cum p (Jf π k) m : ℤ) ≤ SS p hm π (k + t) + (cum p (Jf π (k + t)) m : ℤ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have ih := ih (by omega)
    have e := tsp_end p hm (Jf π (k+t)) (Jf π (k+t+1))
    have hd : dd p hm π (k+t) = delay p hm (Jf π (k+t)) (Jf π (k+t+1)) := by
      unfold dd; rw [if_pos (by omega)]
    have := SS_succ p hm π (k+t)
    rw [show k + (t+1) = k + t + 1 by ring]
    linarith


theorem order_key (hp : ∀ ℓ r, 0 < p ℓ r) (B : Fin (N+1) → ℕ) (hB : IsNoWaitSchedule p B)
    (j k : Fin (N+1)) (hjk : j ≠ k) (hlt : B j < B k) :
    ∀ r : ℕ, r < m → B j + cum p j (r + 1) ≤ B k + cum p k r := by
  intro r
  induction r with
  | zero =>
    intro hr
    have h := hB j k hjk ⟨0, hr⟩
    rw [Set.Ico_disjoint_Ico] at h
    simp only [Fin.val_mk] at h
    have h1 := tsp_cum_strict p hp j 0 hr
    have h2 := tsp_cum_strict p hp k 0 hr
    have h3 := tsp_cum_zero p j
    have h4 := tsp_cum_zero p k
    omega
  | succ r ih =>
    intro hr
    have ih := ih (by omega)
    have h := hB j k hjk ⟨r+1, hr⟩
    rw [Set.Ico_disjoint_Ico] at h
    simp only [Fin.val_mk] at h
    have h1 := tsp_cum_strict p hp j (r+1) hr
    have h2 := tsp_cum_strict p hp k (r+1) hr
    have h3 := tsp_cum_strict p hp k r (by omega)
    omega

theorem sort_exists (hp : ∀ ℓ r, 0 < p ℓ r) (B : Fin (N+1) → ℕ) (hB : IsNoWaitSchedule p B) :
    ∃ π : Fin (N+1) ≃ Fin (N+1), ∀ k : ℕ, k < N →
      dd p hm π k ≤ (B (Jf π (k+1)) : ℤ) - (B (Jf π k) : ℤ) := by
  have hinj : ∀ j k : Fin (N+1), j ≠ k → B j ≠ B k := by
    intro j k hjk heq
    have h := hB j k hjk ⟨0, hm⟩
    rw [Set.Ico_disjoint_Ico] at h
    simp only [Fin.val_mk] at h
    have h1 := tsp_cum_strict p hp j 0 hm
    have h2 := tsp_cum_strict p hp k 0 hm
    have h3 := tsp_cum_zero p j
    have h4 := tsp_cum_zero p k
    omega
  refine ⟨Tuple.sort B, ?_⟩
  intro k hk
  have hmono := Tuple.monotone_sort B
  set π := Tuple.sort B with hπ
  have hle : B (π ⟨k, by omega⟩) ≤ B (π ⟨k+1, by omega⟩) :=
    hmono (show (⟨k, by omega⟩ : Fin (N+1)) ≤ ⟨k+1, by omega⟩ from by simp [Fin.le_def])
  have hne : π ⟨k, by omega⟩ ≠ π ⟨k+1, by omega⟩ := by
    intro h
    have := π.injective h
    simp [Fin.ext_iff] at this
  have hlt : B (π ⟨k, by omega⟩) < B (π ⟨k+1, by omega⟩) :=
    lt_of_le_of_ne hle (hinj _ _ hne)
  have e1 : Jf π k = π ⟨k, by omega⟩ := by
    unfold Jf; exact congrArg π (Fin.ext (by simp only; omega))
  have e2 : Jf π (k+1) = π ⟨k+1, by omega⟩ := by
    unfold Jf; exact congrArg π (Fin.ext (by simp only; omega))
  rw [e1, e2]
  have hd : dd p hm π k = delay p hm (π ⟨k, by omega⟩) (π ⟨k+1, by omega⟩) := by
    unfold dd; rw [if_pos hk, e1, e2]
  rw [hd]
  have key := order_key p hp B hB _ _ hne hlt
  apply tsp_c_le
  intro r
  have := key r.val r.isLt
  have : ((B (π ⟨k, by omega⟩) : ℕ) : ℤ) + (cum p (π ⟨k, by omega⟩) (r.val+1) : ℤ) ≤
      (B (π ⟨k+1, by omega⟩) : ℤ) + (cum p (π ⟨k+1, by omega⟩) r.val : ℤ) := by exact_mod_cast this
  linarith

theorem SS_le (π : Fin (N+1) ≃ Fin (N+1)) (B : Fin (N+1) → ℕ)
    (h : ∀ k : ℕ, k < N → dd p hm π k ≤ (B (Jf π (k+1)) : ℤ) - (B (Jf π k) : ℤ)) :
    ∀ k : ℕ, k ≤ N → SS p hm π k ≤ (B (Jf π k) : ℤ) - (B (Jf π 0) : ℤ) := by
  intro k
  induction k with
  | zero => intro _; simp [SS]
  | succ k ih =>
    intro hk
    have := ih (by omega)
    have := h k (by omega)
    rw [SS_succ]
    linarith

end seq

theorem tsp_core {n m : ℕ} (p : Fin n → Fin m → ℕ) (hm : 0 < m)
    (hp : ∀ ℓ r, 0 < p ℓ r) (y : ℕ) :
    ((∃ B, IsNoWaitSchedule p B ∧ ∀ ℓ, completion p B ℓ ≤ y) ↔
        ∃ π : Fin n ≃ Fin n, pathMakespan p hm π ≤ (y : ℤ)) ∧
      ((∃ B, IsNoWaitSchedule p B ∧ ∑ ℓ, completion p B ℓ ≤ y) ↔
        ∃ π : Fin n ≃ Fin n, pathTotalCompletion p hm π ≤ (y : ℤ)) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have hB : IsNoWaitSchedule p (fun ℓ : Fin 0 => ℓ.elim0) := fun j => j.elim0
    refine ⟨⟨fun _ => ⟨Equiv.refl _, by simp [pathMakespan]⟩, fun _ => ?_⟩,
      ⟨fun _ => ⟨Equiv.refl _, by simp [pathTotalCompletion]⟩, fun _ => ?_⟩⟩
    · exact ⟨fun ℓ => ℓ.elim0, hB, fun ℓ => ℓ.elim0⟩
    · exact ⟨fun ℓ => ℓ.elim0, hB, by simp⟩
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rintro ⟨B, hB, hC⟩
      obtain ⟨π, hπ⟩ := sort_exists p hm hp B hB
      refine ⟨π, ?_⟩
      rw [pm_eq]
      have h1 := SS_le p hm π B hπ N le_rfl
      have h2 := hC (π (Fin.last N))
      have h3 : Jf π N = π (Fin.last N) := by simpa using Jf_fin π (Fin.last N)
      rw [h3] at h1
      unfold completion at h2
      have h2' : (B (π (Fin.last N)) : ℤ) + (cum p (π (Fin.last N)) m : ℤ) ≤ y := by exact_mod_cast h2
      have : (0:ℤ) ≤ B (Jf π 0) := by positivity
      linarith
    · rintro ⟨π, hπ⟩
      obtain ⟨B, hB, hBπ⟩ := build p hm π
      refine ⟨B, hB, fun ℓ => ?_⟩
      obtain ⟨k, rfl⟩ := π.surjective ℓ
      rw [pm_eq] at hπ
      have h1 := GG_mono p hm π k.val (N - k.val) (by have := k.isLt; omega)
      have hk := k.isLt
      rw [show k.val + (N - k.val) = N by omega] at h1
      rw [Jf_fin] at h1
      have h3 : Jf π N = π (Fin.last N) := by simpa using Jf_fin π (Fin.last N)
      rw [h3] at h1
      have := hBπ k
      unfold completion
      have : ((B (π k) + cum p (π k) m : ℕ) : ℤ) ≤ y := by
        push_cast; linarith
      exact_mod_cast this
    · rintro ⟨B, hB, hC⟩
      obtain ⟨π, hπ⟩ := sort_exists p hm hp B hB
      refine ⟨π, ?_⟩
      rw [pt_eq]
      have hC' : ((∑ ℓ, completion p B ℓ : ℕ) : ℤ) ≤ y := by exact_mod_cast hC
      have e : ∑ ℓ, completion p B ℓ = ∑ k, completion p B (π k) :=
        (Equiv.sum_comp π (fun ℓ => completion p B ℓ)).symm
      rw [e] at hC'
      push_cast at hC'
      refine le_trans ?_ hC'
      apply Finset.sum_le_sum
      intro k _
      have h1 := SS_le p hm π B hπ k.val (by have := k.isLt; omega)
      rw [Jf_fin] at h1
      unfold completion
      have : (0:ℤ) ≤ B (Jf π 0) := by positivity
      push_cast
      linarith
    · rintro ⟨π, hπ⟩
      obtain ⟨B, hB, hBπ⟩ := build p hm π
      refine ⟨B, hB, ?_⟩
      rw [pt_eq] at hπ
      have e : ∑ ℓ, completion p B ℓ = ∑ k, completion p B (π k) :=
        (Equiv.sum_comp π (fun ℓ => completion p B ℓ)).symm
      rw [e]
      have : ((∑ k, completion p B (π k) : ℕ) : ℤ) ≤ y := by
        push_cast
        refine le_trans (le_of_eq ?_) hπ
        apply Finset.sum_congr rfl
        intro k _
        unfold completion
        push_cast
        rw [hBπ k]
      exact_mod_cast this


section ham
variable {N : ℕ} (adj : Fin (N+1) → Fin (N+1) → Bool) (ι : Fin (N+1) → Fin (N+1) → ℕ)
  (lam mu : ℕ) (π : Fin (N+1) ≃ Fin (N+1))

def ee (i : ℕ) : ℕ := if adj (Jf π i) (Jf π (i+1)) = true then 0 else 1

def EE : ℕ := ∑ i ∈ Finset.range N, ee adj π i

theorem Jf_ne (i : ℕ) (hi : i < N) : Jf π i ≠ Jf π (i+1) := by
  intro h
  have := π.injective h
  simp only [Fin.mk.injEq] at this
  omega

theorem hp_pos (hι : Admissible (N+1) ι) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu) :
    ∀ ℓ r, 0 < procTimes adj ι lam mu ℓ r := by
  intro ℓ r
  have := procTimes_pos_core adj ι lam mu hι hlam hmu ℓ r
  unfold procTimes
  omega

theorem cumm (hι : Admissible (N+1) ι) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu) (ℓ : Fin (N+1)) :
    (cum (procTimes adj ι lam mu) ℓ (numMachines (N+1)) : ℤ) = (numMachines (N+1) : ℤ) * mu := by
  rw [cum_eq_ps adj ι lam mu hι hlam hmu ℓ _ le_rfl]
  apply le_antisymm
  · apply ps_le_of_not_pos adj ι lam mu ℓ _ hlam
    rintro ⟨k, hk, h⟩
    have := (hι.1 ℓ k hk.symm).2
    unfold numMachines at h
    omega
  · apply ps_ge_of_not_neg adj ι lam mu ℓ _ hlam
    rintro ⟨j, hj, h⟩
    have := (hι.1 j ℓ hj).2
    unfold numMachines at h
    omega

theorem dd_eq (hι : Admissible (N+1) ι) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu) (i : ℕ)
    (hi : i < N) :
    dd (procTimes adj ι lam mu) (numMachines_pos _) π i = mu + 2 * lam + 2 * (ee adj π i : ℤ) := by
  unfold dd
  rw [if_pos hi, delay_construction_core adj ι lam mu hι hlam hmu _ _ (Jf_ne π i hi)]
  by_cases h : adj (Jf π i) (Jf π (i+1)) = true
  · simp [ee, h]
  · simp [ee, h]

theorem SS_eq (hι : Admissible (N+1) ι) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu) :
    ∀ k : ℕ, k ≤ N → SS (procTimes adj ι lam mu) (numMachines_pos _) π k =
      k * (mu + 2 * lam) + 2 * ((∑ i ∈ Finset.range k, ee adj π i : ℕ) : ℤ) := by
  intro k
  induction k with
  | zero => intro _; simp [SS]
  | succ k ih =>
    intro hk
    rw [SS_succ, ih (by omega), dd_eq adj ι lam mu π hι hlam hmu k (by omega), Finset.sum_range_succ]
    push_cast
    ring

theorem pm_val (hι : Admissible (N+1) ι) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu) :
    pathMakespan (procTimes adj ι lam mu) (numMachines_pos _) π =
      N * (mu + 2 * lam) + 2 * (EE adj π : ℤ) + (numMachines (N+1) : ℤ) * mu := by
  rw [pm_eq, SS_eq adj ι lam mu π hι hlam hmu N le_rfl, cumm adj ι lam mu hι hlam hmu]
  unfold EE
  ring

theorem ee_zero_iff : EE adj π = 0 ↔ ∀ i, i < N → adj (Jf π i) (Jf π (i+1)) = true := by
  unfold EE
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h i hi
    have := h i (Finset.mem_range.mpr hi)
    unfold ee at this
    by_contra hc
    rw [if_neg hc] at this
    omega
  · intro h i hi
    unfold ee
    rw [if_pos (h i (Finset.mem_range.mp hi))]

theorem ham_iff : HasHamiltonPath adj ↔ ∃ π : Fin (N+1) ≃ Fin (N+1), EE adj π = 0 := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, (ee_zero_iff adj σ).2 ?_⟩
    intro i hi
    have := hσ ⟨i, by omega⟩ (by simp only; omega)
    have e1 : Jf σ i = σ ⟨i, by omega⟩ := Jf_fin σ ⟨i, by omega⟩
    have e2 : Jf σ (i+1) = σ ⟨i+1, by omega⟩ := Jf_fin σ ⟨i+1, by omega⟩
    rw [e1, e2]
    exact this
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    intro i h
    have := (ee_zero_iff adj σ).1 hσ i.val (by omega)
    rw [Jf_fin σ i, show Jf σ (i.val+1) = σ ⟨i.val+1, h⟩ from Jf_fin σ ⟨i.val+1, h⟩] at this
    exact this

end ham

theorem thm5a_core {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ)
    (hι : Admissible n ι) (lam mu : ℕ) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu) :
    HasHamiltonPath adj ↔
      ∃ B, IsNoWaitSchedule (procTimes adj ι lam mu) B ∧
        ∀ ℓ, completion (procTimes adj ι lam mu) B ℓ ≤
          (n - 1) * (mu + 2 * lam) + numMachines n * mu := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    constructor
    · intro _
      have hp : ∀ ℓ r, 0 < procTimes adj ι lam mu ℓ r := fun ℓ => ℓ.elim0
      exact (tsp_core (procTimes adj ι lam mu) (numMachines_pos 0) hp _).1.2
        ⟨Equiv.refl _, by simp [pathMakespan]; positivity⟩
    · intro _
      exact ⟨Equiv.refl _, fun i => i.elim0⟩
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    rw [ham_iff adj, (tsp_core (procTimes adj ι lam mu) (numMachines_pos _)
      (hp_pos adj ι lam mu hι hlam hmu) _).1]
    apply exists_congr
    intro π
    rw [pm_val adj ι lam mu π hι hlam hmu]
    have : (N + 1 - 1) = N := by omega
    rw [this]
    push_cast
    constructor
    · intro h; rw [h]; simp
    · intro h
      have : (EE adj π : ℤ) ≤ 0 := by linarith
      omega


section ham2
variable {N : ℕ} (adj : Fin (N+1) → Fin (N+1) → Bool) (ι : Fin (N+1) → Fin (N+1) → ℕ)
  (lam mu : ℕ) (π : Fin (N+1) ≃ Fin (N+1))

theorem pt_val (hι : Admissible (N+1) ι) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu) :
    pathTotalCompletion (procTimes adj ι lam mu) (numMachines_pos _) π =
      (∑ k ∈ Finset.range (N+1), k : ℕ) * (mu + 2 * lam : ℤ)
        + 2 * ((∑ k ∈ Finset.range (N+1), ∑ i ∈ Finset.range k, ee adj π i : ℕ) : ℤ)
        + (N + 1 : ℤ) * ((numMachines (N+1) : ℤ) * mu) := by
  rw [pt_eq]
  have h1 : ∀ k : Fin (N+1), (SS (procTimes adj ι lam mu) (numMachines_pos _) π k.val
      + (cum (procTimes adj ι lam mu) (π k) (numMachines (N+1)) : ℤ)) =
      (fun k : ℕ => SS (procTimes adj ι lam mu) (numMachines_pos _) π k
        + (numMachines (N+1) : ℤ) * mu) k.val := by
    intro k
    simp only
    rw [cumm adj ι lam mu hι hlam hmu]
  rw [Finset.sum_congr rfl (fun k _ => h1 k),
    Fin.sum_univ_eq_sum_range (fun k : ℕ => SS (procTimes adj ι lam mu) (numMachines_pos _) π k
        + (numMachines (N+1) : ℤ) * mu) (N+1)]
  have h2 : ∀ k ∈ Finset.range (N+1), SS (procTimes adj ι lam mu) (numMachines_pos _) π k
        + (numMachines (N+1) : ℤ) * mu =
      (k : ℤ) * (mu + 2 * lam) + 2 * ((∑ i ∈ Finset.range k, ee adj π i : ℕ) : ℤ)
        + (numMachines (N+1) : ℤ) * mu := by
    intro k hk
    rw [SS_eq adj ι lam mu π hι hlam hmu k (by have := Finset.mem_range.mp hk; omega)]
  rw [Finset.sum_congr rfl h2]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range]
  push_cast
  simp
  ring

end ham2

theorem thm5b_core {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ)
    (hι : Admissible n ι) (lam mu : ℕ) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu) :
    HasHamiltonPath adj ↔
      ∃ B, IsNoWaitSchedule (procTimes adj ι lam mu) B ∧
        ((∑ ℓ, completion (procTimes adj ι lam mu) B ℓ : ℕ) : ℚ) ≤
          (1 / 2 : ℚ) * n * ((n : ℚ) - 1) * ((mu : ℚ) + 2 * lam) +
            (n : ℚ) * (numMachines n : ℚ) * mu := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    constructor
    · intro _
      exact ⟨fun ℓ => ℓ.elim0, fun j => j.elim0, by simp⟩
    · intro _
      exact ⟨Equiv.refl _, fun i => i.elim0⟩
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    set T : ℕ := ∑ k ∈ Finset.range (N+1), k with hTdef
    have hT2 : T * 2 = (N + 1) * (N + 1 - 1) := Finset.sum_range_id_mul_two (N+1)
    have hTq : (T : ℚ) = (1/2 : ℚ) * (N + 1) * N := by
      have : (T : ℚ) * 2 = (N + 1) * N := by
        have := congrArg (fun x : ℕ => (x : ℚ)) hT2
        simpa using this
      linarith
    set y : ℕ := T * (mu + 2 * lam) + (N + 1) * numMachines (N+1) * mu with hy
    have hyq : ∀ B : Fin (N+1) → ℕ,
        (((∑ ℓ, completion (procTimes adj ι lam mu) B ℓ : ℕ) : ℚ) ≤
          (1 / 2 : ℚ) * ((N + 1 : ℕ) : ℚ) * (((N + 1 : ℕ) : ℚ) - 1) * ((mu : ℚ) + 2 * lam) +
            ((N + 1 : ℕ) : ℚ) * (numMachines (N+1) : ℚ) * mu) ↔
          (∑ ℓ, completion (procTimes adj ι lam mu) B ℓ) ≤ y := by
      intro B
      have : (1 / 2 : ℚ) * ((N + 1 : ℕ) : ℚ) * (((N + 1 : ℕ) : ℚ) - 1) * ((mu : ℚ) + 2 * lam) +
            ((N + 1 : ℕ) : ℚ) * (numMachines (N+1) : ℚ) * mu = (y : ℚ) := by
        rw [hy]; push_cast
        rw [hTq]; push_cast; ring
      rw [this]
      exact_mod_cast Iff.rfl
    simp_rw [hyq]
    rw [ham_iff adj, (tsp_core (procTimes adj ι lam mu) (numMachines_pos _)
      (hp_pos adj ι lam mu hι hlam hmu) y).2]
    apply exists_congr
    intro π
    rw [pt_val adj ι lam mu π hι hlam hmu, ← hTdef]
    have hyz : (y : ℤ) = (T : ℤ) * (mu + 2 * lam : ℤ) + (N + 1 : ℤ) * ((numMachines (N+1) : ℤ) * mu) := by
      rw [hy]; push_cast; ring
    rw [hyz]
    set F : ℕ := ∑ k ∈ Finset.range (N+1), ∑ i ∈ Finset.range k, ee adj π i with hF
    have hEF : EE adj π ≤ F := by
      have := Finset.single_le_sum (f := fun k => ∑ i ∈ Finset.range k, ee adj π i)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_self N))
      exact this
    have hFE : EE adj π = 0 → F = 0 := by
      intro h
      apply Finset.sum_eq_zero
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have : ∑ i ∈ Finset.range k, ee adj π i ≤ EE adj π :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
      omega
    constructor
    · intro h
      have := hFE h
      rw [this]
      simp
    · intro h
      have : (F : ℤ) ≤ 0 := by push_cast at h ⊢; linarith
      omega

end SchedComplexity.NoWait

open SchedComplexity.NoWait


theorem solution {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ)
    (hι : Admissible n ι) (lam mu : ℕ) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu) :
    HasHamiltonPath adj ↔
      ∃ B, IsNoWaitSchedule (procTimes adj ι lam mu) B ∧
        ((∑ ℓ, completion (procTimes adj ι lam mu) B ℓ : ℕ) : ℚ) ≤
          (1 / 2 : ℚ) * n * ((n : ℚ) - 1) * ((mu : ℚ) + 2 * lam) +
            (n : ℚ) * (numMachines n : ℚ) * mu := by
  exact thm5b_core adj ι hι lam mu hlam hmu
