-- Prove2me | solution 1 for SchedComplexity.Partition.theorem_3b_value_eq_k
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:29:23.646512+00:00
-- url     : https://prove2.me/submissions/a332ee1f-5e53-427e-85bb-53a20ffb8728

import Mathlib
import Definitions.Def_SchedComplexity_Partition_PartitionProblem
import Definitions.Def_SchedComplexity_Partition_TwoMachineModel
import Definitions.Def_SchedComplexity_Partition_Constructions



namespace SchedComplexity.Partition
open Finset

section gen
variable {n : ℕ}

lemma sched_disj_sum (σ : Schedule n) (p : Fin n → ℕ) (hf : σ.IsFeasible p)
    (K : Finset (Fin n)) (hK : ∀ j ∈ K, ∀ k ∈ K, σ.machine j = σ.machine k)
    (lo hi : ℕ) (h1 : ∀ k ∈ K, lo ≤ σ.start k) (h2 : ∀ k ∈ K, σ.start k + p k ≤ hi) :
    ∑ k ∈ K, p k ≤ hi - lo := by
  have hdisj : (K : Set (Fin n)).PairwiseDisjoint
      (fun k => Finset.Ico (σ.start k) (σ.start k + p k)) := by
    intro j hj k hk hjk
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_Ico] at hx1 hx2
    exact hf j k hjk (hK j hj k hk) ⟨by omega, by omega, by omega, by omega⟩
  have hcard := Finset.card_biUnion hdisj
  have hsub : K.biUnion (fun k => Finset.Ico (σ.start k) (σ.start k + p k)) ⊆ Finset.Ico lo hi := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨k, hk, hx⟩ := hx
    rw [Finset.mem_Ico] at hx ⊢
    have := h1 k hk
    have := h2 k hk
    omega
  have hle := Finset.card_le_card hsub
  have e : ∑ k ∈ K, (Finset.Ico (σ.start k) (σ.start k + p k)).card = ∑ k ∈ K, p k :=
    Finset.sum_congr rfl (fun k _ => by simp)
  rw [hcard, e] at hle
  simpa using hle

lemma e_le (σ : Schedule n) (p : Fin n → ℕ) (hf : σ.IsFeasible p) (J : Finset (Fin n))
    (hJ : ∀ j ∈ J, ∀ k ∈ J, σ.machine j = σ.machine k) (j : Fin n) (hj : j ∈ J) (hpj : 0 < p j) :
    ∑ k ∈ J, (if σ.start k < σ.start j then p k else 0) ≤ σ.start j := by
  rw [← Finset.sum_filter]
  have := sched_disj_sum σ p hf (J.filter (fun k => σ.start k < σ.start j))
    (fun a ha b hb => hJ a (mem_filter.1 ha).1 b (mem_filter.1 hb).1) 0 (σ.start j)
    (fun _ _ => Nat.zero_le _) ?_
  · simpa using this
  · intro k hk
    rw [mem_filter] at hk
    obtain ⟨hkJ, hlt⟩ := hk
    by_cases hpk : p k = 0
    · omega
    · have hne : k ≠ j := by rintro rfl; omega
      have h := hf k j hne (hJ k hkJ j hj)
      by_contra hcon
      exact h ⟨by omega, hpj, by omega, by omega⟩

lemma l_le (σ : Schedule n) (p : Fin n → ℕ) (hf : σ.IsFeasible p) (J : Finset (Fin n))
    (hJ : ∀ j ∈ J, ∀ k ∈ J, σ.machine j = σ.machine k) (P : ℕ)
    (hC : ∀ k ∈ J, σ.start k + p k ≤ P) (j : Fin n) (hj : j ∈ J) (hpj : 0 < p j) :
    ∑ k ∈ J, (if σ.start j < σ.start k then p k else 0) ≤ P - (σ.start j + p j) := by
  have e : ∑ k ∈ J, (if σ.start j < σ.start k then p k else 0) =
      ∑ k ∈ J.filter (fun k => σ.start j < σ.start k ∧ 0 < p k), p k := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : p k = 0
    · simp [h]
    · have : 0 < p k := Nat.pos_of_ne_zero h
      simp [this]
  rw [e]
  refine sched_disj_sum σ p hf _
    (fun a ha b hb => hJ a (mem_filter.1 ha).1 b (mem_filter.1 hb).1) _ P ?_ ?_
  · intro k hk
    rw [mem_filter] at hk
    obtain ⟨hkJ, hlt, hpk⟩ := hk
    have hne : k ≠ j := by rintro rfl; omega
    have h := hf k j hne (hJ k hkJ j hj)
    by_contra hcon
    exact h ⟨hpk, hpj, by omega, by omega⟩
  · intro k hk
    exact hC k (mem_filter.1 hk).1

lemma decomp (σ : Schedule n) (p : Fin n → ℕ) (hf : σ.IsFeasible p) (J : Finset (Fin n))
    (hJ : ∀ j ∈ J, ∀ k ∈ J, σ.machine j = σ.machine k) (j : Fin n) (hj : j ∈ J) (hpj : 0 < p j) :
    ∑ k ∈ J, p k = (∑ k ∈ J, (if σ.start k < σ.start j then p k else 0)) + p j +
      ∑ k ∈ J, (if σ.start j < σ.start k then p k else 0) := by
  have h : ∀ k ∈ J, p k = (if σ.start k < σ.start j then p k else 0) +
      (if k = j then p k else 0) + (if σ.start j < σ.start k then p k else 0) := by
    intro k hk
    by_cases hkj : k = j
    · subst hkj; simp
    · by_cases hpk : p k = 0
      · simp [hpk]
      · have hpk' : 0 < p k := Nat.pos_of_ne_zero hpk
        have hne : σ.start k ≠ σ.start j := by
          intro heq
          exact hf k j hkj (hJ k hk j hj) ⟨hpk', hpj, by omega, by omega⟩
        split_ifs <;> omega
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp [hj]

lemma sym_pair (J : Finset (Fin n)) (p : Fin n → ℕ) (g h : Fin n → ℕ)
    (hg : ∀ j ∈ J, ∀ k ∈ J, 0 < p j → 0 < p k → j ≠ k → g j ≠ g k)
    (hh : ∀ j ∈ J, ∀ k ∈ J, 0 < p j → 0 < p k → j ≠ k → h j ≠ h k) :
    ∑ j ∈ J, ∑ k ∈ J, (if g k < g j then p j * p k else 0) =
      ∑ j ∈ J, ∑ k ∈ J, (if h k < h j then p j * p k else 0) := by
  have key : ∀ g : Fin n → ℕ, (∀ j ∈ J, ∀ k ∈ J, 0 < p j → 0 < p k → j ≠ k → g j ≠ g k) →
      2 * ∑ j ∈ J, ∑ k ∈ J, (if g k < g j then p j * p k else 0) =
        ∑ j ∈ J, ∑ k ∈ J, (if j ≠ k then p j * p k else 0) := by
    intro g hg
    have hsw : ∑ j ∈ J, ∑ k ∈ J, (if g k < g j then p j * p k else 0) =
        ∑ j ∈ J, ∑ k ∈ J, (if g j < g k then p j * p k else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [mul_comm]
    rw [two_mul]
    nth_rewrite 2 [hsw]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    by_cases hpj : p j = 0
    · simp [hpj]
    by_cases hpk : p k = 0
    · simp [hpk]
    by_cases hjk : j = k
    · subst hjk; simp
    · have := hg j hj k hk (Nat.pos_of_ne_zero hpj) (Nat.pos_of_ne_zero hpk) hjk
      rcases lt_or_gt_of_ne this with h1 | h1
      · simp [h1, h1.not_gt, hjk]
      · simp [h1, h1.not_gt, hjk]
  have := key g hg
  have := key h hh
  omega

lemma pair_split (J : Finset (Fin n)) (p : Fin n → ℕ) (st : Fin n → ℕ)
    (hinj : ∀ j ∈ J, ∀ k ∈ J, 0 < p j → 0 < p k → j ≠ k → st j ≠ st k) :
    ∑ j ∈ J, ∑ k ∈ J, (if j ≤ k then p j * p k else 0) =
      ∑ j ∈ J, p j * p j + ∑ j ∈ J, ∑ k ∈ J, (if st k < st j then p j * p k else 0) := by
  have h1 : ∀ j k : Fin n, (if j ≤ k then p j * p k else 0) =
      (if j = k then p j * p j else 0) + (if j < k then p j * p k else 0) := by
    intro j k
    by_cases h : j = k
    · subst h; simp
    · have : j ≤ k ↔ j < k := ⟨fun hh => lt_of_le_of_ne hh h, le_of_lt⟩
      simp [h, this]
  have h2 : ∑ j ∈ J, ∑ k ∈ J, (if j ≤ k then p j * p k else 0) =
      ∑ j ∈ J, ∑ k ∈ J, (if j = k then p j * p j else 0) +
        ∑ j ∈ J, ∑ k ∈ J, (if j < k then p j * p k else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => h1 j k)
  have h3 : ∑ j ∈ J, ∑ k ∈ J, (if j = k then p j * p j else 0) = ∑ j ∈ J, p j * p j := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp [hj]
  have h4 : ∑ j ∈ J, ∑ k ∈ J, (if j < k then p j * p k else 0) =
      ∑ j ∈ J, ∑ k ∈ J, (if ((k : Fin n) : ℕ) < ((j : Fin n) : ℕ) then p j * p k else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [mul_comm]
    rfl
  have h5 := sym_pair J p st (fun j => (j : ℕ)) hinj
    (fun j hj k hk _ _ hjk => fun h => hjk (Fin.ext h))
  rw [h2, h3, h4, h5]


lemma hinj_of_feas (σ : Schedule n) (p : Fin n → ℕ) (hf : σ.IsFeasible p) (J : Finset (Fin n))
    (hJ : ∀ j ∈ J, ∀ k ∈ J, σ.machine j = σ.machine k) :
    ∀ j ∈ J, ∀ k ∈ J, 0 < p j → 0 < p k → j ≠ k → σ.start j ≠ σ.start k := by
  intro j hj k hk hpj hpk hjk heq
  exact hf j k hjk (hJ j hj k hk) ⟨hpj, hpk, by omega, by omega⟩

lemma mul_e (σ : Schedule n) (p : Fin n → ℕ) (J : Finset (Fin n)) :
    ∑ j ∈ J, p j * (∑ k ∈ J, (if σ.start k < σ.start j then p k else 0)) =
      ∑ j ∈ J, ∑ k ∈ J, (if σ.start k < σ.start j then p j * p k else 0) := by
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  split_ifs <;> simp

lemma key_ge (σ : Schedule n) (p : Fin n → ℕ) (hf : σ.IsFeasible p) (J : Finset (Fin n))
    (hJ : ∀ j ∈ J, ∀ k ∈ J, σ.machine j = σ.machine k) :
    ∑ j ∈ J, ∑ k ∈ J, (if j ≤ k then p j * p k else 0) ≤ ∑ j ∈ J, p j * σ.completion p j := by
  rw [pair_split J p σ.start (hinj_of_feas σ p hf J hJ), ← mul_e, add_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun j hj => ?_)
  by_cases hp : p j = 0
  · simp [hp]
  · have := e_le σ p hf J hJ j hj (Nat.pos_of_ne_zero hp)
    rw [← mul_add]
    apply Nat.mul_le_mul_left
    unfold Schedule.completion
    omega

lemma key_eq (σ : Schedule n) (p : Fin n → ℕ) (hf : σ.IsFeasible p) (J : Finset (Fin n))
    (hJ : ∀ j ∈ J, ∀ k ∈ J, σ.machine j = σ.machine k)
    (hC : ∀ j ∈ J, σ.completion p j ≤ ∑ k ∈ J, p k) :
    ∑ j ∈ J, p j * σ.completion p j = ∑ j ∈ J, ∑ k ∈ J, (if j ≤ k then p j * p k else 0) := by
  refine le_antisymm ?_ (key_ge σ p hf J hJ)
  rw [pair_split J p σ.start (hinj_of_feas σ p hf J hJ), ← mul_e, add_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun j hj => ?_)
  by_cases hp : p j = 0
  · simp [hp]
  · have hpos := Nat.pos_of_ne_zero hp
    have hC' : ∀ k ∈ J, σ.start k + p k ≤ ∑ k ∈ J, p k := fun k hk => hC k hk
    have h1 := l_le σ p hf J hJ _ hC' j hj hpos
    have h2 := decomp σ p hf J hJ j hj hpos
    have h3 := hC j hj
    unfold Schedule.completion at h3 ⊢
    rw [← mul_add]
    apply Nat.mul_le_mul_left
    omega

/-- Assignment schedule. -/
def asched (m : Fin n → Fin 2) (p : Fin n → ℕ) : Schedule n :=
  ⟨m, fun j => ∑ k ∈ Finset.univ.filter (fun k => m k = m j ∧ k < j), p k⟩

lemma asched_comp (m : Fin n → Fin 2) (p : Fin n → ℕ) (j : Fin n) :
    (asched m p).completion p j =
      ∑ k ∈ Finset.univ.filter (fun k => m k = m j ∧ k ≤ j), p k := by
  unfold Schedule.completion asched
  have : Finset.univ.filter (fun k => m k = m j ∧ k ≤ j) =
      insert j (Finset.univ.filter (fun k => m k = m j ∧ k < j)) := by
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h2 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h1, h⟩
    · rintro (h | ⟨h1, h2⟩)
      · subst h; exact ⟨rfl, le_refl _⟩
      · exact ⟨h1, le_of_lt h2⟩
  rw [this, Finset.sum_insert (by simp)]
  simp [add_comm]

lemma asched_feas (m : Fin n → Fin 2) (p : Fin n → ℕ) : (asched m p).IsFeasible p := by
  have key : ∀ j k : Fin n, j < k → m j = m k →
      (asched m p).start j + p j ≤ (asched m p).start k := by
    intro j k hjk hm
    show (∑ i ∈ Finset.univ.filter (fun i => m i = m j ∧ i < j), p i) + p j ≤
      ∑ i ∈ Finset.univ.filter (fun i => m i = m k ∧ i < k), p i
    have hdisj : Disjoint (Finset.univ.filter (fun i => m i = m j ∧ i < j)) {j} := by
      simp
    rw [← Finset.sum_singleton p j, ← Finset.sum_union hdisj]
    apply Finset.sum_le_sum_of_subset
    intro i hi
    simp only [mem_union, mem_filter, mem_univ, true_and, mem_singleton] at hi ⊢
    rcases hi with ⟨h1, h2⟩ | h
    · exact ⟨by rw [← hm]; exact h1, lt_trans h2 hjk⟩
    · subst h; exact ⟨hm, hjk⟩
  intro j k hjk hm ⟨hpj, hpk, h1, h2⟩
  have hm' : m j = m k := hm
  rcases lt_or_gt_of_ne hjk with h | h
  · have := key j k h hm'
    simp only [asched] at *
    omega
  · have := key k j h hm'.symm
    simp only [asched] at *
    omega

lemma asched_nonidle (m : Fin n → Fin 2) (p : Fin n → ℕ) (j : Fin n) :
    (asched m p).completion p j ≤
      ∑ k ∈ Finset.univ.filter (fun k => (asched m p).machine k = (asched m p).machine j), p k := by
  rw [asched_comp]
  apply Finset.sum_le_sum_of_subset
  intro k hk
  simp only [mem_filter, mem_univ, true_and] at hk ⊢
  exact hk.1

end gen

lemma fin2_ne (x y : Fin 2) (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
  revert x y; decide

lemma sched_split_aux (a : List ℕ) (S : Finset (Fin a.length)) (σ : Schedule a.length)
    (hS : ∀ j, σ.machine j = 0 ↔ j ∈ S) :
    (∀ j ∈ S, ∀ k ∈ S, σ.machine j = σ.machine k) ∧
    (∀ j ∈ Sᶜ, ∀ k ∈ Sᶜ, σ.machine j = σ.machine k) ∧
    (∀ j ∈ S, Finset.univ.filter (fun k => σ.machine k = σ.machine j) = S) ∧
    (∀ j ∈ Sᶜ, Finset.univ.filter (fun k => σ.machine k = σ.machine j) = Sᶜ) := by
  have hne : ∀ j, j ∈ Sᶜ → σ.machine j ≠ 0 := by
    intro j hj h
    exact (Finset.mem_compl.1 hj) ((hS j).1 h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj k hk; rw [(hS j).2 hj, (hS k).2 hk]
  · intro j hj k hk; exact fin2_ne _ _ (hne j hj) (hne k hk)
  · intro j hj
    ext k
    simp only [mem_filter, mem_univ, true_and]
    rw [(hS j).2 hj]; exact hS k
  · intro j hj
    ext k
    simp only [mem_filter, mem_univ, true_and, Finset.mem_compl]
    constructor
    · intro h hk
      have := (hS k).2 hk
      exact hne j hj (h.symm.trans this)
    · intro hk
      exact fin2_ne _ _ (fun h => hk ((hS k).1 h)) (hne j hj)

theorem theorem_3b_value_eq_k_core (a : List ℕ) (S : Finset (Fin a.length))
    (σ : Schedule a.length) (hS : ∀ j, σ.machine j = 0 ↔ j ∈ S) :
    (σ.IsNonIdle (procB a) → σ.sumWC (procB a) (procB a) = kVal a S) ∧
      (σ.IsFeasible (procB a) → kVal a S ≤ σ.sumWC (procB a) (procB a)) := by
  obtain ⟨h1, h2, h3, h4⟩ := sched_split_aux a S σ hS
  have hsum : σ.sumWC (procB a) (procB a) =
      ∑ j ∈ S, procB a j * σ.completion (procB a) j +
        ∑ j ∈ Sᶜ, procB a j * σ.completion (procB a) j := by
    unfold Schedule.sumWC
    exact (Finset.sum_add_sum_compl S _).symm
  have hk : kVal a S = ∑ j ∈ S, ∑ k ∈ S, (if j ≤ k then procB a j * procB a k else 0) +
      ∑ j ∈ Sᶜ, ∑ k ∈ Sᶜ, (if j ≤ k then procB a j * procB a k else 0) := rfl
  constructor
  · rintro ⟨hf, hC⟩
    rw [hsum, hk, key_eq σ _ hf S h1, key_eq σ _ hf Sᶜ h2]
    · intro j hj
      have := hC j; rwa [h4 j hj] at this
    · intro j hj
      have := hC j; rwa [h3 j hj] at this
  · intro hf
    rw [hsum, hk]
    exact add_le_add (key_ge σ _ hf S h1) (key_ge σ _ hf Sᶜ h2)


lemma kVal_univ (a : List ℕ) : kVal a Finset.univ = pairSum a := by
  simp [kVal, pairSum]

lemma pair_decomp (a : List ℕ) (S : Finset (Fin a.length)) :
    pairSum a = kVal a S + (∑ j ∈ S, a.get j) * (∑ j ∈ Sᶜ, a.get j) := by
  set f : Fin a.length → Fin a.length → ℕ := fun j k => if j ≤ k then a.get j * a.get k else 0 with hf
  have e1 : pairSum a = ∑ j, ∑ k, f j k := rfl
  have e2 : ∀ j, ∑ k, f j k = ∑ k ∈ S, f j k + ∑ k ∈ Sᶜ, f j k :=
    fun j => (Finset.sum_add_sum_compl S _).symm
  have e3 : ∑ j, ∑ k, f j k = ∑ j ∈ S, ∑ k, f j k + ∑ j ∈ Sᶜ, ∑ k, f j k :=
    (Finset.sum_add_sum_compl S _).symm
  have e4 : ∑ j ∈ S, ∑ k, f j k = ∑ j ∈ S, ∑ k ∈ S, f j k + ∑ j ∈ S, ∑ k ∈ Sᶜ, f j k := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun j _ => e2 j)
  have e5 : ∑ j ∈ Sᶜ, ∑ k, f j k = ∑ j ∈ Sᶜ, ∑ k ∈ S, f j k + ∑ j ∈ Sᶜ, ∑ k ∈ Sᶜ, f j k := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun j _ => e2 j)
  have e6 : ∑ j ∈ Sᶜ, ∑ k ∈ S, f j k = ∑ k ∈ S, ∑ j ∈ Sᶜ, f j k := Finset.sum_comm
  have e7 : ∑ j ∈ S, ∑ k ∈ Sᶜ, f j k + ∑ k ∈ S, ∑ j ∈ Sᶜ, f j k =
      (∑ j ∈ S, a.get j) * (∑ j ∈ Sᶜ, a.get j) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hjk : j ≠ k := fun h => (Finset.mem_compl.1 hk) (h ▸ hj)
    simp only [hf]
    rcases lt_or_gt_of_ne hjk with h | h
    · simp [h.le, h.not_ge]
    · simp [h.le, h.not_ge, mul_comm]
  have e8 : kVal a S = ∑ j ∈ S, ∑ k ∈ S, f j k + ∑ j ∈ Sᶜ, ∑ k ∈ Sᶜ, f j k := rfl
  rw [e1, e3, e4, e5, e6, e8, ← e7]
  ring

theorem theorem_3b_k_identity_core (a : List ℕ) (S : Finset (Fin a.length)) :
    let c : ℝ := ((∑ j ∈ S, a.get j : ℕ) : ℝ) - (totalA a : ℝ) / 2
    (kVal a S : ℝ) =
        (kVal a Finset.univ : ℝ) -
          ((∑ j ∈ S, a.get j : ℕ) : ℝ) * ((∑ j ∈ Sᶜ, a.get j : ℕ) : ℝ) ∧
      (kVal a Finset.univ : ℝ) -
          ((∑ j ∈ S, a.get j : ℕ) : ℝ) * ((∑ j ∈ Sᶜ, a.get j : ℕ) : ℝ) =
        (pairSum a : ℝ) - ((totalA a : ℝ) / 2 + c) * ((totalA a : ℝ) / 2 - c) ∧
      (pairSum a : ℝ) - ((totalA a : ℝ) / 2 + c) * ((totalA a : ℝ) / 2 - c) = yB a + c ^ 2 := by
  intro c
  have hpd : (pairSum a : ℝ) = (kVal a S : ℝ) +
      ((∑ j ∈ S, a.get j : ℕ) : ℝ) * ((∑ j ∈ Sᶜ, a.get j : ℕ) : ℝ) := by
    exact_mod_cast pair_decomp a S
  have hA : (totalA a : ℝ) = ((∑ j ∈ S, a.get j : ℕ) : ℝ) + ((∑ j ∈ Sᶜ, a.get j : ℕ) : ℝ) := by
    have : totalA a = (∑ j ∈ S, a.get j) + ∑ j ∈ Sᶜ, a.get j := by
      unfold totalA; exact (Finset.sum_add_sum_compl S _).symm
    exact_mod_cast this
  have hc : c = ((∑ j ∈ S, a.get j : ℕ) : ℝ) - (totalA a : ℝ) / 2 := rfl
  rw [kVal_univ]
  refine ⟨by linarith, ?_, ?_⟩
  · have h1 : (totalA a : ℝ) / 2 + c = ((∑ j ∈ S, a.get j : ℕ) : ℝ) := by rw [hc]; ring
    have h2 : (totalA a : ℝ) / 2 - c = ((∑ j ∈ Sᶜ, a.get j : ℕ) : ℝ) := by
      rw [hc]; linarith
    rw [h1, h2]
  · unfold yB; ring


open Classical in
lemma part_sched (a : List ℕ) (S : Finset (Fin a.length)) :
    ∃ σ : Schedule a.length, (∀ j, σ.machine j = 0 ↔ j ∈ S) ∧ σ.IsNonIdle (procA a) := by
  refine ⟨asched (fun j => if j ∈ S then 0 else 1) (procA a), ?_, ?_⟩
  · intro j
    show (if j ∈ S then (0 : Fin 2) else 1) = 0 ↔ j ∈ S
    by_cases h : j ∈ S <;> simp [h]
  · exact ⟨asched_feas _ _, fun j => asched_nonidle _ _ j⟩

lemma comp_le_half (a : List ℕ) (S : Finset (Fin a.length)) (σ : Schedule a.length)
    (hS : ∀ j, σ.machine j = 0 ↔ j ∈ S) (hni : σ.IsNonIdle (procA a))
    (hSS : ∑ j ∈ S, a.get j = ∑ j ∈ Sᶜ, a.get j) (j : Fin a.length) :
    σ.completion (procA a) j ≤ ∑ j ∈ S, a.get j := by
  obtain ⟨h1, h2, h3, h4⟩ := sched_split_aux a S σ hS
  have := hni.2 j
  by_cases hj : j ∈ S
  · rw [h3 j hj] at this; exact this
  · have hj' : j ∈ Sᶜ := Finset.mem_compl.2 hj
    rw [h4 j hj'] at this
    rw [hSS]; exact this

lemma totalA_split (a : List ℕ) (S : Finset (Fin a.length)) :
    totalA a = (∑ j ∈ S, a.get j) + ∑ j ∈ Sᶜ, a.get j := by
  unfold totalA; exact (Finset.sum_add_sum_compl S _).symm

theorem theorem_3a_equivalence_core (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    PartitionSolvable a ↔
      ∃ σ : Schedule a.length, σ.IsFeasible (procA a) ∧
        ∀ j, (σ.completion (procA a) j : ℝ) ≤ yA a := by
  constructor
  · rintro ⟨S, hSS⟩
    obtain ⟨σ, hS, hni⟩ := part_sched a S
    refine ⟨σ, hni.1, fun j => ?_⟩
    have h1 := comp_le_half a S σ hS hni hSS j
    have h2 := totalA_split a S
    unfold yA
    have h3 : ((totalA a : ℕ) : ℝ) = 2 * ((∑ j ∈ S, a.get j : ℕ) : ℝ) := by
      rw [h2, ← hSS]; push_cast; ring
    have h4 : ((σ.completion (procA a) j : ℕ) : ℝ) ≤ ((∑ j ∈ S, a.get j : ℕ) : ℝ) := by
      exact_mod_cast h1
    linarith
  · rintro ⟨σ, hf, hC⟩
    classical
    set S : Finset (Fin a.length) := Finset.univ.filter (fun j => σ.machine j = 0) with hSdef
    have hS : ∀ j, σ.machine j = 0 ↔ j ∈ S := by intro j; simp [hSdef]
    obtain ⟨h1, h2, h3, h4⟩ := sched_split_aux a S σ hS
    have hC' : ∀ j, σ.start j + procA a j ≤ ⌊yA a⌋₊ := by
      intro j
      exact Nat.le_floor (hC j)
    have hy : (0 : ℝ) ≤ yA a := by unfold yA; positivity
    have b1 := sched_disj_sum σ (procA a) hf S h1 0 ⌊yA a⌋₊ (fun _ _ => Nat.zero_le _) (fun k _ => hC' k)
    have b2 := sched_disj_sum σ (procA a) hf Sᶜ h2 0 ⌊yA a⌋₊ (fun _ _ => Nat.zero_le _) (fun k _ => hC' k)
    have f1 : ((⌊yA a⌋₊ : ℕ) : ℝ) ≤ yA a := Nat.floor_le hy
    have c1 : ((∑ j ∈ S, a.get j : ℕ) : ℝ) ≤ yA a := by
      have : (∑ j ∈ S, a.get j) ≤ ⌊yA a⌋₊ := by simpa [procA] using b1
      calc _ ≤ ((⌊yA a⌋₊ : ℕ) : ℝ) := by exact_mod_cast this
        _ ≤ _ := f1
    have c2 : ((∑ j ∈ Sᶜ, a.get j : ℕ) : ℝ) ≤ yA a := by
      have : (∑ j ∈ Sᶜ, a.get j) ≤ ⌊yA a⌋₊ := by simpa [procA] using b2
      calc _ ≤ ((⌊yA a⌋₊ : ℕ) : ℝ) := by exact_mod_cast this
        _ ≤ _ := f1
    have hA : (totalA a : ℝ) = ((∑ j ∈ S, a.get j : ℕ) : ℝ) + ((∑ j ∈ Sᶜ, a.get j : ℕ) : ℝ) := by
      exact_mod_cast totalA_split a S
    refine ⟨S, ?_⟩
    have : ((∑ j ∈ S, a.get j : ℕ) : ℝ) = ((∑ j ∈ Sᶜ, a.get j : ℕ) : ℝ) := by
      unfold yA at c1 c2; linarith
    exact_mod_cast this

theorem theorem_3b_equivalence_core (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    PartitionSolvable a ↔
      ∃ σ : Schedule a.length, σ.IsFeasible (procB a) ∧
        (σ.sumWC (procB a) (procB a) : ℝ) ≤ yB a := by
  constructor
  · rintro ⟨S, hSS⟩
    obtain ⟨σ, hS, hni⟩ := part_sched a S
    refine ⟨σ, hni.1, ?_⟩
    have hv := (theorem_3b_value_eq_k_core a S σ hS).1 hni
    have hid := theorem_3b_k_identity_core a S
    dsimp only at hid
    obtain ⟨i1, i2, i3⟩ := hid
    have hA : (totalA a : ℝ) = 2 * ((∑ j ∈ S, a.get j : ℕ) : ℝ) := by
      have := totalA_split a S
      rw [← hSS] at this; rw [this]; push_cast; ring
    have hc : ((∑ j ∈ S, a.get j : ℕ) : ℝ) - (totalA a : ℝ) / 2 = 0 := by rw [hA]; ring
    rw [hv]
    rw [i1, i2, i3, hc]
    simp
  · rintro ⟨σ, hf, hle⟩
    classical
    set S : Finset (Fin a.length) := Finset.univ.filter (fun j => σ.machine j = 0) with hSdef
    have hS : ∀ j, σ.machine j = 0 ↔ j ∈ S := by intro j; simp [hSdef]
    have hk := (theorem_3b_value_eq_k_core a S σ hS).2 hf
    have hk' : (kVal a S : ℝ) ≤ (σ.sumWC (procB a) (procB a) : ℝ) := by exact_mod_cast hk
    have hid := theorem_3b_k_identity_core a S
    dsimp only at hid
    obtain ⟨i1, i2, i3⟩ := hid
    have hkeq := i1.trans (i2.trans i3)
    have hsq : (((∑ j ∈ S, a.get j : ℕ) : ℝ) - (totalA a : ℝ) / 2) ^ 2 ≤ 0 := by linarith
    have hc : ((∑ j ∈ S, a.get j : ℕ) : ℝ) - (totalA a : ℝ) / 2 = 0 := by
      have := sq_nonneg (((∑ j ∈ S, a.get j : ℕ) : ℝ) - (totalA a : ℝ) / 2)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm hsq this)
    have hA : (totalA a : ℝ) = ((∑ j ∈ S, a.get j : ℕ) : ℝ) + ((∑ j ∈ Sᶜ, a.get j : ℕ) : ℝ) := by
      exact_mod_cast totalA_split a S
    refine ⟨S, ?_⟩
    have : ((∑ j ∈ S, a.get j : ℕ) : ℝ) = ((∑ j ∈ Sᶜ, a.get j : ℕ) : ℝ) := by linarith
    exact_mod_cast this

end SchedComplexity.Partition

open SchedComplexity.Partition


theorem solution (a : List ℕ) (S : Finset (Fin a.length))
    (σ : Schedule a.length) (hS : ∀ j, σ.machine j = 0 ↔ j ∈ S) :
    (σ.IsNonIdle (procB a) → σ.sumWC (procB a) (procB a) = kVal a S) ∧
      (σ.IsFeasible (procB a) → kVal a S ≤ σ.sumWC (procB a) (procB a)) := by
  exact theorem_3b_value_eq_k_core a S σ hS
