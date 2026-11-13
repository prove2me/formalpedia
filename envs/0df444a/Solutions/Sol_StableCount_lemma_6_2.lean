-- Prove2me | solution 1 for StableCount.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T23:14:42.213199+00:00
-- url     : https://prove2.me/submissions/471ad9a4-e7d4-453b-81f1-f21d04e71143

import Mathlib
import Definitions.Def_StableCount_Groups

section
namespace StableCount

open StableMatching

namespace Dev.L52

variable {n : ℕ}

/-- the partner of the person `p` of sex `s` in the `m`-th matching of the chain -/
def partner (Q : Member n) : Sex → Fin (Q.R + 1) → Fin n → Fin n
  | .man, m, p => Q.μ m p
  | .woman, m, p => (Q.μ m).symm p

theorem moves_iff (Q : Member n) (s : Sex) (i : Fin Q.R) (p : Fin n) :
    Q.moves s i p ↔ partner Q s i.castSucc p ≠ partner Q s i.succ p := by
  cases s <;> rfl

/-- no move before `m` means the partner is the initial one -/
theorem partner_eq_zero (Q : Member n) (s : Sex) (p : Fin n) (m : Fin (Q.R + 1))
    (h : ∀ k : Fin Q.R, (k : ℕ) < m → ¬ Q.moves s k p) : partner Q s m p = partner Q s 0 p := by
  obtain ⟨m, hm⟩ := m
  induction m with
  | zero => rfl
  | succ m ih =>
    have hmR : m < Q.R := by omega
    have h1 := ih (by omega) (fun k hk => h k (by simp only [Fin.val_mk] at hk ⊢; omega))
    have h2 := h ⟨m, hmR⟩ (by simp)
    rw [moves_iff] at h2
    push_neg at h2
    rw [← h1]
    exact h2.symm

/-- no move between `a` and `b` -/
theorem partner_eq_of_no_move (Q : Member n) (s : Sex) (p : Fin n) (a b : Fin (Q.R + 1))
    (hab : a ≤ b) (h : ∀ k : Fin Q.R, (a : ℕ) ≤ k → (k : ℕ) < b → ¬ Q.moves s k p) :
    partner Q s b p = partner Q s a p := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have hab' : a ≤ b := hab
  induction b, hab' using Nat.le_induction with
  | base => rfl
  | succ b hab' ih =>
    have hbR : b < Q.R := by omega
    have h1 := ih (by omega) (Fin.mk_le_mk.mpr hab')
      (fun k hk1 hk2 => h k hk1 (by simp only [Fin.val_mk] at hk2 ⊢; omega))
    have h2 := h ⟨b, hbR⟩ (by simpa using hab') (by simp)
    rw [moves_iff] at h2
    push_neg at h2
    rw [← h1]
    exact h2.symm

theorem shares_of_consecutive (Q : Member n) (w : Fin n) (i j : Fin Q.R) (hij : i < j)
    (hi : Q.moves .woman i w) (hj : Q.moves .woman j w)
    (hno : ∀ k : Fin Q.R, i < k → k < j → ¬ Q.moves .woman k w) : Q.sharesMan i j := by
  have hsame : (Q.μ j.castSucc).symm w = (Q.μ i.succ).symm w := by
    have := partner_eq_of_no_move Q .woman w i.succ j.castSucc
      (by rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact hij) (fun k hk1 hk2 => by
        apply hno k
        · simp only [Fin.val_succ] at hk1; exact hk1
        · simpa using hk2)
    simpa [partner] using this
  refine ⟨(Q.μ i.succ).symm w, ?_, ?_⟩
  · show Q.μ i.castSucc _ ≠ Q.μ i.succ _
    intro heq
    apply hi
    have h1 : Q.μ i.succ ((Q.μ i.succ).symm w) = w := Equiv.apply_symm_apply _ _
    have h2 : (Q.μ i.castSucc).symm w = (Q.μ i.succ).symm w := by
      rw [Equiv.symm_apply_eq]; rw [heq, h1]
    exact h2
  · show Q.μ j.castSucc _ ≠ Q.μ j.succ _
    intro heq
    apply hj
    have h1 : Q.μ j.castSucc ((Q.μ i.succ).symm w) = w := by
      rw [← hsame]; exact Equiv.apply_symm_apply _ _
    have h3 : Q.μ j.succ ((Q.μ i.succ).symm w) = w := by rw [← heq]; exact h1
    have h4 : (Q.μ j.succ).symm w = (Q.μ i.succ).symm w := by
      rw [Equiv.symm_apply_eq]; exact h3.symm
    rw [hsame, h4]

open Classical in
theorem le_of_woman (Q : Member n) (w : Fin n) :
    ∀ (d : ℕ) (i j : Fin Q.R), (j : ℕ) - i = d → i < j → Q.moves .woman i w →
      Q.moves .woman j w → Q.le i j := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i j hd hij hi hj
    set T : Finset (Fin Q.R) := Finset.univ.filter fun k => i < k ∧ Q.moves .woman k w with hT
    have hTne : T.Nonempty := ⟨j, by simp [hT, hij, hj]⟩
    set k0 := T.min' hTne with hk0
    have hk0T : k0 ∈ T := Finset.min'_mem _ _
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hk0T
    have hk0le : k0 ≤ j := Finset.min'_le _ _ (by simp [hT, hij, hj])
    have hcons : Q.sharesMan i k0 := by
      apply shares_of_consecutive Q w i k0 hk0T.1 hi hk0T.2
      intro k hk1 hk2 hmv
      have : k ∈ T := by simp [hT, hk1, hmv]
      exact absurd (Finset.min'_le _ _ this) (not_le.mpr hk2)
    have h1 : Q.le i k0 := Relation.ReflTransGen.single ⟨hk0T.1, hcons⟩
    rcases hk0le.lt_or_eq with hlt | heq
    · have h2 : Q.le k0 j := ih ((j : ℕ) - k0) (by have := hk0T.1; rw [Fin.lt_def] at this; omega)
        k0 j rfl hlt hk0T.2 hj
      exact Relation.ReflTransGen.trans h1 h2
    · rw [← heq]; exact h1

theorem le_of_chain (Q : Member n) (s : Sex) (p : Fin n) (i j : Fin Q.R) (hij : i < j)
    (hi : Q.moves s i p) (hj : Q.moves s j p) : Q.le i j := by
  cases s
  · exact Relation.ReflTransGen.single ⟨hij, p, hi, hj⟩
  · exact le_of_woman Q p _ i j rfl hij hi hj

theorem mem_chainOf (Q : Member n) (s : Sex) (p : Fin n) (i : Fin Q.R) :
    i ∈ Q.chainOf s p ↔ Q.moves s i p := by
  unfold Member.chainOf
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem first_spec (Q : Member n) (v : Fin n) (hv : v ∈ Q.V) :
    Q.moves .man (Q.first v hv) v ∧ ∀ k : Fin Q.R, k < Q.first v hv → ¬ Q.moves .man k v := by
  have hne : (Q.chainOf .man v).Nonempty := Finset.card_pos.mp (Finset.mem_filter.mp hv).2
  refine ⟨?_, fun k hk hmv => ?_⟩
  · exact (mem_chainOf Q .man v _).mp (Finset.min'_mem (Q.chainOf .man v) hne)
  · have hk' : k ∈ Q.chainOf .man v := (mem_chainOf Q .man v k).mpr hmv
    exact absurd (Finset.min'_le _ k hk') (not_le.mpr hk)

theorem man_eq_first (Q : Member n) (v : Fin n) (hv : v ∈ Q.V) (m : Fin (Q.R + 1))
    (hm : (m : ℕ) ≤ Q.first v hv) : Q.μ m v = Q.μ 0 v := by
  obtain ⟨-, h2⟩ := first_spec Q v hv
  have := partner_eq_zero Q .man v m (fun k hk hmv =>
    h2 k (by rw [Fin.lt_def]; omega) hmv)
  simpa [partner] using this

theorem first_mem_chain (Q : Member n) (s : Sex) (v : Fin n) (hv : v ∈ Q.V) :
    Q.first v hv ∈ Q.chainOf s (Q.person s v) := by
  obtain ⟨h1, h2⟩ := first_spec Q v hv
  rw [mem_chainOf]
  cases s
  · exact h1
  · have e0 := man_eq_first Q v hv
    change (Q.μ (Q.first v hv).castSucc).symm (Q.μ 0 v) ≠ (Q.μ (Q.first v hv).succ).symm (Q.μ 0 v)
    have a1 : (Q.μ (Q.first v hv).castSucc).symm (Q.μ 0 v) = v := by
      rw [Equiv.symm_apply_eq]; exact (e0 _ (by simp)).symm
    intro heq
    have h3 : (Q.μ (Q.first v hv).succ).symm (Q.μ 0 v) = v := by rw [← heq]; exact a1
    rw [Equiv.symm_apply_eq] at h3
    have h4 := e0 (Q.first v hv).castSucc (by simp)
    have h5 : Q.μ (Q.first v hv).castSucc v ≠ Q.μ (Q.first v hv).succ v := h1
    exact h5 (by rw [h4, ← h3])

end Dev.L52

end StableCount
end

section
namespace StableCount

open StableMatching

namespace Dev.L62

open Dev.L52

variable {n : ℕ}

section basic

variable (Q : Member n)

theorem le_idx {i j : Fin Q.R} (h : Q.le i j) : i ≤ j := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact ih.trans hbc.1.le

theorem le_rfl' (i : Fin Q.R) : Q.le i i := Relation.ReflTransGen.refl

theorem le_tr {a b c : Fin Q.R} (h1 : Q.le a b) (h2 : Q.le b c) : Q.le a c :=
  Relation.ReflTransGen.trans h1 h2

theorem mem_down' (i j : Fin Q.R) : j ∈ Q.down i ↔ Q.le j i := by
  simp [Member.down]

theorem mem_participants (k : Fin Q.R) (w : Fin n) :
    w ∈ Q.participants k ↔ Q.moves .man k w := by
  simp [Member.participants]

theorem step_lt (k : Fin Q.R) : MatchingLT Q.I (Q.μ k.castSucc) (Q.μ k.succ) :=
  (Q.chain.2.2 k).2.2.1

theorem rank_mono (m : Fin n) (i j : Fin (Q.R + 1)) (hij : i ≤ j) :
    Q.I.manRank m (Q.μ i m) ≤ Q.I.manRank m (Q.μ j m) := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  have hij' : i ≤ j := hij
  induction j, hij' using Nat.le_induction with
  | base => exact le_refl _
  | succ j hij' ih =>
    have hjR : j < Q.R := by omega
    refine (ih (by omega) (Fin.mk_le_mk.mpr hij')).trans ?_
    have := (step_lt Q ⟨j, hjR⟩).1 m
    simpa using this

theorem rank_strict (m : Fin n) (k : Fin Q.R) (hk : Q.moves .man k m) :
    Q.I.manRank m (Q.μ k.castSucc m) < Q.I.manRank m (Q.μ k.succ m) := by
  refine lt_of_le_of_ne ((step_lt Q k).1 m) ?_
  intro heq
  exact hk ((Q.I.manRank m).injective heq)

theorem no_return (m : Fin n) (k : Fin Q.R) (hk : Q.moves .man k m) (i j : Fin (Q.R + 1))
    (hi : i ≤ k.castSucc) (hj : k.succ ≤ j) : Q.μ j m ≠ Q.μ i m := by
  intro heq
  have h1 := rank_mono Q m i k.castSucc hi
  have h2 := rank_strict Q m k hk
  have h3 := rank_mono Q m k.succ j hj
  rw [heq] at h3
  exact absurd (h1.trans_lt (h2.trans_le h3)) (lt_irrefl _)

theorem new_from (k : Fin Q.R) (m : Fin n) (hm : Q.moves .man k m) :
    ∃ m', Q.moves .man k m' ∧ m' ≠ m ∧ Q.μ k.succ m = Q.μ k.castSucc m' := by
  have hm0 : Q.μ k.castSucc m ≠ Q.μ k.succ m := hm
  set m' := (Q.μ k.castSucc).symm (Q.μ k.succ m) with hm'
  have e1 : Q.μ k.castSucc m' = Q.μ k.succ m := by simp [hm']
  have hne : m' ≠ m := by
    intro h
    rw [h] at e1
    exact hm0 e1
  refine ⟨m', ?_, hne, e1.symm⟩
  intro hno'
  rw [e1] at hno'
  exact hne ((Q.μ k.succ).injective hno').symm

theorem exists_move (k : Fin Q.R) : ∃ m, Q.moves .man k m := by
  by_contra hcon
  push_neg at hcon
  apply (step_lt Q k).2
  exact Equiv.ext fun m => not_not.mp (hcon m)

theorem two_le_participants (k : Fin Q.R) : 2 ≤ (Q.participants k).card := by
  obtain ⟨m, hm⟩ := exists_move Q k
  obtain ⟨m', hm', hne, -⟩ := new_from Q k m hm
  have hsub : ({m', m} : Finset (Fin n)) ⊆ Q.participants k := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rw [mem_participants]
    rcases hw with rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rwa [Finset.card_pair hne] at this

theorem swap_eq (k : Fin Q.R) (y z : Fin n) (hp : Q.participants k = {y, z}) (_hyz : y ≠ z) :
    Q.μ k.succ y = Q.μ k.castSucc z := by
  have hy : Q.moves .man k y := (mem_participants Q k y).mp (by rw [hp]; simp)
  obtain ⟨m', hm', hne, he⟩ := new_from Q k y hy
  have : m' ∈ Q.participants k := (mem_participants Q k m').mpr hm'
  rw [hp] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h
  · exact absurd h hne
  · rw [he, h]

theorem mem_V_of_moves (k : Fin Q.R) (w : Fin n) (hw : Q.moves .man k w) : w ∈ Q.V := by
  unfold Member.V
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold Member.dL Member.deg
  exact Finset.card_pos.mpr ⟨k, (mem_chainOf Q .man w k).mpr hw⟩

theorem isFirst_iff (w : Fin n) (i : Fin Q.R) :
    Q.IsFirst w i ↔ Q.moves .man i w ∧ ∀ k, k < i → ¬ Q.moves .man k w := by
  constructor
  · rintro ⟨hw, rfl⟩
    exact first_spec Q w hw
  · rintro ⟨h1, h2⟩
    have hw := mem_V_of_moves Q i w h1
    refine ⟨hw, ?_⟩
    obtain ⟨g1, g2⟩ := first_spec Q w hw
    rcases lt_trichotomy (Q.first w hw) i with hlt | heq | hgt
    · exact absurd g1 (h2 _ hlt)
    · exact heq
    · exact absurd h1 (g2 _ hgt)

theorem isFirst_unique {w : Fin n} {i j : Fin Q.R} (hi : Q.IsFirst w i) (hj : Q.IsFirst w j) :
    i = j := by
  obtain ⟨hv, rfl⟩ := hi
  obtain ⟨hv', rfl⟩ := hj
  rfl

theorem mem_support_of (B j : Fin Q.R) (hj : Q.le j B) (w : Fin n) (hw : Q.moves .man j w) :
    w ∈ Q.support B := by
  have hwV := mem_V_of_moves Q j w hw
  simp only [Member.support, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨Q.first w hwV, ⟨hwV, rfl⟩, ?_⟩
  obtain ⟨g1, g2⟩ := first_spec Q w hwV
  rcases (le_of_not_gt (fun h => g2 j h hw) : Q.first w hwV ≤ j).lt_or_eq with hlt | heq
  · exact le_tr Q (le_of_chain Q .man w _ _ hlt g1 hw) hj
  · rw [heq]; exact hj

theorem man_eq_zero (w : Fin n) (m : Fin (Q.R + 1))
    (h : ∀ k : Fin Q.R, (k : ℕ) < m → ¬ Q.moves .man k w) : Q.μ m w = Q.μ 0 w :=
  partner_eq_zero Q .man w m h

theorem man_const (w : Fin n) (a b : Fin (Q.R + 1)) (hab : a ≤ b)
    (h : ∀ k : Fin Q.R, (a : ℕ) ≤ k → (k : ℕ) < b → ¬ Q.moves .man k w) : Q.μ b w = Q.μ a w :=
  partner_eq_of_no_move Q .man w a b hab h

theorem woman_const (w : Fin n) (a b : Fin (Q.R + 1)) (hab : a ≤ b)
    (h : ∀ k : Fin Q.R, (a : ℕ) ≤ k → (k : ℕ) < b → ¬ Q.moves .woman k w) :
    (Q.μ b).symm w = (Q.μ a).symm w :=
  partner_eq_of_no_move Q .woman w a b hab h

theorem moves_woman_iff (k : Fin Q.R) (m : Fin n) :
    Q.moves .woman k (Q.μ k.castSucc m) ↔ Q.moves .man k m := by
  show (Q.μ k.castSucc).symm (Q.μ k.castSucc m) ≠ (Q.μ k.succ).symm (Q.μ k.castSucc m) ↔
    Q.μ k.castSucc m ≠ Q.μ k.succ m
  rw [Equiv.symm_apply_apply]
  constructor
  · intro h1 h2
    apply h1
    rw [h2, Equiv.symm_apply_apply]
  · intro h1 h2
    apply h1
    rw [Equiv.eq_symm_apply] at h2
    exact h2.symm

/-- after time `j`, the man `m` and his wife `μ j m` move again at the same time -/
theorem pair_moves (m : Fin n) (j : Fin (Q.R + 1)) :
    (∃ k : Fin Q.R, j ≤ k.castSucc ∧ Q.moves .man k m) ↔
      (∃ k : Fin Q.R, j ≤ k.castSucc ∧ Q.moves .woman k (Q.μ j m)) := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨k0, hk0, hmin⟩ := WellFounded.has_min wellFounded_lt
      {k : Fin Q.R | j ≤ k.castSucc ∧ Q.moves .man k m} ⟨k, hk⟩
    obtain ⟨hk0j, hk0m⟩ := hk0
    have e : Q.μ k0.castSucc m = Q.μ j m := by
      apply man_const Q m j k0.castSucc hk0j
      intro k' hk1 hk2 hmv
      apply hmin k' ⟨?_, hmv⟩
      · rw [Fin.lt_def]; simpa using hk2
      · rw [Fin.le_def]; simpa using hk1
    refine ⟨k0, hk0j, ?_⟩
    rw [← e, moves_woman_iff]
    exact hk0m
  · rintro ⟨k, hk⟩
    obtain ⟨k0, hk0, hmin⟩ := WellFounded.has_min wellFounded_lt
      {k : Fin Q.R | j ≤ k.castSucc ∧ Q.moves .woman k (Q.μ j m)} ⟨k, hk⟩
    obtain ⟨hk0j, hk0m⟩ := hk0
    have e : (Q.μ k0.castSucc).symm (Q.μ j m) = (Q.μ j).symm (Q.μ j m) := by
      apply woman_const Q _ j k0.castSucc hk0j
      intro k' hk1 hk2 hmv
      apply hmin k' ⟨?_, hmv⟩
      · rw [Fin.lt_def]; simpa using hk2
      · rw [Fin.le_def]; simpa using hk1
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_eq] at e
    refine ⟨k0, hk0j, ?_⟩
    rw [e, moves_woman_iff] at hk0m
    exact hk0m

theorem card_chain_iff {R : ℕ} (C S : Finset (Fin R)) (B : Fin R) (hSC : S ⊆ C)
    (hS : ∀ k ∈ S, k ≤ B) (hC : ∀ k ∈ C, k ∉ S → B < k) :
    C.card = S.card ↔ ∀ k, B < k → k ∉ C := by
  constructor
  · intro hc k hk hkC
    have hEq : S = C := Finset.eq_of_subset_of_card_le hSC (by omega)
    rw [← hEq] at hkC
    exact absurd (hS k hkC) (not_le.mpr hk)
  · intro h
    have hsub : C ⊆ S := by
      intro k hk
      by_contra hkS
      exact h k (hC k hk hkS) hk
    rw [Finset.Subset.antisymm hsub hSC]

end basic

section struct

variable (Q : Member n)

theorem lt_succ_le {R : ℕ} {a b : Fin R} (h : a < b) : a.succ ≤ b.castSucc := by
  rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact Fin.lt_def.mp h

theorem lt_of_succ_le {R : ℕ} {a k : Fin R} (h : (a.succ : ℕ) ≤ k) : a < k := by
  rw [Fin.lt_def]; simp only [Fin.val_succ] at h; omega

theorem lt_of_castSucc {R : ℕ} {k b : Fin R} (h : (k : ℕ) < b.castSucc) : k < b := by
  rw [Fin.lt_def]; simpa using h

/-- Lemma 5.4: the structure of an exceptional swap. -/
theorem exc_struct (B : Fin Q.R) (x : Fin n) (hx : Q.IsFirst x B)
    (h1 : (Q.firstGroup B).card = 1) (h3 : Q.s B = 3) :
    ∃ A' y z, A' < B ∧ y ≠ z ∧ y ≠ x ∧ z ≠ x ∧ Q.participants A' = {y, z} ∧
      Q.IsFirst y A' ∧ Q.IsFirst z A' ∧ Q.down B = {A', B} ∧ Q.participants B = {y, x} ∧
      (∀ k, A' < k → k < B → ¬ Q.moves .man k y) := by
  have hxF : x ∈ Q.firstGroup B := by simp [Member.firstGroup]; exact hx
  rw [isFirst_iff] at hx
  obtain ⟨hxB, hxpre⟩ := hx
  have hxS : x ∈ Q.support B := mem_support_of Q B B (le_rfl' Q B) x hxB
  have hcard : (Q.support B \ {x}).card = 2 := by
    rw [Finset.card_sdiff_of_subset (by simpa using hxS)]
    unfold Member.s at h3
    rw [h3]; simp
  obtain ⟨y, z, hyz, hS⟩ := Finset.card_eq_two.mp hcard
  have hyS : y ∈ Q.support B ∧ y ≠ x := by
    have : y ∈ Q.support B \ {x} := by rw [hS]; simp
    simpa using this
  have hzS : z ∈ Q.support B ∧ z ≠ x := by
    have : z ∈ Q.support B \ {x} := by rw [hS]; simp
    simpa using this
  have hFG : ∀ w, Q.IsFirst w B → w = x := by
    intro w hw
    have hwF : w ∈ Q.firstGroup B := by simp [Member.firstGroup]; exact hw
    exact Finset.card_le_one.mp h1.le w hwF x hxF
  have hpart : ∀ j, Q.le j B → j ≠ B → Q.participants j = {y, z} := by
    intro j hj hjB
    have hjlt : j < B := lt_of_le_of_ne (le_idx Q hj) hjB
    have hsub : Q.participants j ⊆ {y, z} := by
      intro w hw
      rw [mem_participants] at hw
      rw [← hS]
      refine Finset.mem_sdiff.mpr ⟨mem_support_of Q B j hj w hw, ?_⟩
      simp only [Finset.mem_singleton]
      rintro rfl
      exact hxpre j hjlt hw
    exact Finset.eq_of_subset_of_card_le hsub
      (by rw [Finset.card_pair hyz]; exact two_le_participants Q j)
  have hfirst_of : ∀ w ∈ Q.support B, w ≠ x → ∃ j, Q.IsFirst w j ∧ Q.le j B ∧ j ≠ B := by
    intro w hw hwx
    simp only [Member.support, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨j, hj, hjB⟩ := hw
    refine ⟨j, hj, hjB, ?_⟩
    rintro rfl
    exact hwx (hFG w hj)
  obtain ⟨A', hyA, hA'B, hA'ne⟩ := hfirst_of y hyS.1 hyS.2
  obtain ⟨A'', hzA, hA''B, hA''ne⟩ := hfirst_of z hzS.1 hzS.2
  have hpA := hpart A' hA'B hA'ne
  have hpA2 := hpart A'' hA''B hA''ne
  have hyA' := hyA
  have hzA' := hzA
  rw [isFirst_iff] at hyA hzA
  have hzmA : Q.moves .man A' z := (mem_participants Q A' z).mp (by rw [hpA]; simp)
  have hymA2 : Q.moves .man A'' y := (mem_participants Q A'' y).mp (by rw [hpA2]; simp)
  have heqA : A'' = A' :=
    le_antisymm (not_lt.mp fun h => hzA.2 _ h hzmA) (not_lt.mp fun h => hyA.2 _ h hymA2)
  subst heqA
  have hymA : Q.moves .man A'' y := hymA2
  have hA'lt : A'' < B := lt_of_le_of_ne (le_idx Q hA'B) hA'ne
  -- partners at the start
  have hz0 : Q.μ A''.castSucc z = Q.μ 0 z :=
    man_eq_zero Q z _ (fun k hk => hzA.2 k (lt_of_castSucc hk))
  have hy0 : Q.μ A''.castSucc y = Q.μ 0 y :=
    man_eq_zero Q y _ (fun k hk => hyA.2 k (lt_of_castSucc hk))
  have hpA' : Q.participants A'' = {z, y} := by rw [hpA, Finset.pair_comm]
  have hyS1 : Q.μ A''.succ y = Q.μ 0 z := by rw [swap_eq Q A'' y z hpA hyz, hz0]
  have hzS1 : Q.μ A''.succ z = Q.μ 0 y := by rw [swap_eq Q A'' z y hpA' hyz.symm, hy0]
  -- the down set
  have hdown : Q.down B = {A'', B} := by
    ext j
    rw [mem_down']
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hj
      by_contra hcon
      push_neg at hcon
      classical
      obtain ⟨j0, hj0, hmin⟩ := WellFounded.has_min wellFounded_lt
        {j : Fin Q.R | Q.le j B ∧ j ≠ A'' ∧ j ≠ B} ⟨j, hj, hcon.1, hcon.2⟩
      obtain ⟨hj0B, hj0A, hj0B'⟩ := hj0
      have hp0 := hpart j0 hj0B hj0B'
      have hy0m : Q.moves .man j0 y := (mem_participants Q j0 y).mp (by rw [hp0]; simp)
      have hz0m : Q.moves .man j0 z := (mem_participants Q j0 z).mp (by rw [hp0]; simp)
      have hAj0 : A'' < j0 :=
        lt_of_le_of_ne (not_lt.mp fun h => hyA.2 _ h hy0m) (Ne.symm hj0A)
      have hj0lt : j0 < B := lt_of_le_of_ne (le_idx Q hj0B) hj0B'
      have hmin' : ∀ k, A'' < k → k < j0 → ∀ w, Q.moves .man j0 w → ¬ Q.moves .man k w := by
        intro k hk1 hk2 w hw hkw
        have hkle : Q.le k B := le_tr Q (le_of_chain Q .man w k j0 hk2 hkw hw) hj0B
        exact hmin k ⟨hkle, hk1.ne', (hk2.trans hj0lt).ne⟩ hk2
      have ey : Q.μ j0.castSucc y = Q.μ 0 z := by
        rw [man_const Q y A''.succ j0.castSucc (lt_succ_le hAj0)
          (fun k hk1 hk2 => hmin' k (lt_of_succ_le hk1) (lt_of_castSucc hk2) y hy0m), hyS1]
      have ez : Q.μ j0.castSucc z = Q.μ 0 y := by
        rw [man_const Q z A''.succ j0.castSucc (lt_succ_le hAj0)
          (fun k hk1 hk2 => hmin' k (lt_of_succ_le hk1) (lt_of_castSucc hk2) z hz0m), hzS1]
      have e1 : Q.μ j0.succ y = Q.μ 0 y := by rw [swap_eq Q j0 y z hp0 hyz, ez]
      refine no_return Q y A'' hymA 0 j0.succ (Fin.zero_le _) ?_ e1
      rw [Fin.le_def]; simp only [Fin.val_succ]; have := Fin.lt_def.mp hAj0; omega
    · rintro (rfl | rfl)
      · exact hA'B
      · exact le_rfl' Q _
  have hpB : ∀ w, Q.moves .man B w → w = x ∨ w = y ∨ w = z := by
    intro w hw
    by_cases hwx : w = x
    · exact Or.inl hwx
    · have : w ∈ Q.support B \ {x} :=
        Finset.mem_sdiff.mpr ⟨mem_support_of Q B B (le_rfl' Q B) w hw, by simpa using hwx⟩
      rw [hS] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      exact Or.inr this
  have hgap : ∀ w, Q.moves .man B w → ∀ k, A'' < k → k < B → ¬ Q.moves .man k w := by
    intro w hw k hk1 hk2 hkw
    have hkle : Q.le k B := le_of_chain Q .man w k B hk2 hkw hw
    have : k ∈ Q.down B := (mem_down' Q B k).mpr hkle
    rw [hdown] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact (h ▸ hk1).false
    · exact (h ▸ hk2).false
  have hxB0 : Q.μ B.castSucc x = Q.μ 0 x :=
    man_eq_zero Q x _ (fun k hk => hxpre k (lt_of_castSucc hk))
  have hyB : Q.moves .man B y → Q.μ B.castSucc y = Q.μ 0 z := by
    intro hm
    rw [man_const Q y A''.succ B.castSucc (lt_succ_le hA'lt)
      (fun k hk1 hk2 => hgap y hm k (lt_of_succ_le hk1) (lt_of_castSucc hk2)), hyS1]
  have hzB : Q.moves .man B z → Q.μ B.castSucc z = Q.μ 0 y := by
    intro hm
    rw [man_const Q z A''.succ B.castSucc (lt_succ_le hA'lt)
      (fun k hk1 hk2 => hgap z hm k (lt_of_succ_le hk1) (lt_of_castSucc hk2)), hzS1]
  have hsucc_le : A''.succ ≤ B.succ := by
    rw [Fin.le_def]; simp only [Fin.val_succ]; have := Fin.lt_def.mp hA'lt; omega
  have hnotboth : ¬ (Q.moves .man B y ∧ Q.moves .man B z) := by
    rintro ⟨hyBm, hzBm⟩
    obtain ⟨m1, hm1, hne1, he1⟩ := new_from Q B y hyBm
    obtain ⟨m2, hm2, hne2, he2⟩ := new_from Q B z hzBm
    have hy' : Q.μ B.succ y = Q.μ 0 x := by
      rcases hpB m1 hm1 with h | h | h
      · rw [he1, h, hxB0]
      · exact absurd h hne1
      · exfalso
        rw [h, hzB hzBm] at he1
        exact no_return Q y A'' hymA 0 B.succ (Fin.zero_le _) hsucc_le he1
    have hz' : Q.μ B.succ z = Q.μ 0 x := by
      rcases hpB m2 hm2 with h | h | h
      · rw [he2, h, hxB0]
      · exfalso
        rw [h, hyB hyBm] at he2
        exact no_return Q z A'' hzmA 0 B.succ (Fin.zero_le _) hsucc_le he2
      · exact absurd h hne2
    exact hyz ((Q.μ B.succ).injective (hy'.trans hz'.symm))
  have hone : Q.moves .man B y ∨ Q.moves .man B z := by
    by_contra hc
    push_neg at hc
    have hsub : Q.participants B ⊆ {x} := by
      intro w hw
      rw [mem_participants] at hw
      rcases hpB w hw with h | h | h
      · simp [h]
      · exact absurd (h ▸ hw) hc.1
      · exact absurd (h ▸ hw) hc.2
    have h2 := two_le_participants Q B
    have h1' := Finset.card_le_card hsub
    rw [Finset.card_singleton] at h1'
    omega
  rcases hone with hyBm | hzBm
  · have hzBn : ¬ Q.moves .man B z := fun h => hnotboth ⟨hyBm, h⟩
    refine ⟨A'', y, z, hA'lt, hyz, hyS.2, hzS.2, hpA, hyA', hzA', hdown, ?_, hgap y hyBm⟩
    ext w
    rw [mem_participants]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hw
      rcases hpB w hw with h | h | h
      · exact Or.inr h
      · exact Or.inl h
      · exact absurd (h ▸ hw) hzBn
    · rintro (h | h)
      · exact h ▸ hyBm
      · exact h ▸ hxB
  · have hyBn : ¬ Q.moves .man B y := fun h => hnotboth ⟨h, hzBm⟩
    refine ⟨A'', z, y, hA'lt, hyz.symm, hzS.2, hyS.2, hpA', hzA', hyA', hdown, ?_, hgap z hzBm⟩
    ext w
    rw [mem_participants]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hw
      rcases hpB w hw with h | h | h
      · exact Or.inr h
      · exact absurd (h ▸ hw) hyBn
      · exact Or.inl h
    · rintro (h | h)
      · exact h ▸ hzBm
      · exact h ▸ hxB

end struct

section assoc

variable (Q : Member n)

/-- `x` is exceptional with first rotation `B = (y, x)`, following the initial swap `A = (y, z)`. -/
def Assoc (A : Fin Q.R) (x y z : Fin n) (B : Fin Q.R) : Prop :=
  Q.IsFirst x B ∧ Q.IsExceptionalSwap B ∧ A < B ∧ y ≠ z ∧ y ≠ x ∧ z ≠ x ∧
    Q.participants A = {y, z} ∧ Q.IsFirst y A ∧ Q.IsFirst z A ∧ Q.down B = {A, B} ∧
    Q.participants B = {y, x} ∧ (∀ k, A < k → k < B → ¬ Q.moves .man k y)

theorem assoc_of_exc (x : Fin n) (B : Fin Q.R) (hx : Q.IsFirst x B)
    (hB : Q.IsExceptionalSwap B) : ∃ A y z, Assoc Q A x y z B := by
  obtain ⟨A', y, z, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := exc_struct Q B x hx hB.1 hB.2
  exact ⟨A', y, z, hx, hB, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem assoc_of_XA (A : Fin Q.R) (x : Fin n) (hx : x ∈ Q.XA A) :
    ∃ y z B, Assoc Q A x y z B := by
  simp only [Member.XA, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨⟨B, hxB, hB⟩, B', hxB', hAB, hne⟩ := hx
  have := isFirst_unique Q hxB hxB'
  subst this
  obtain ⟨A', y, z, hs⟩ := assoc_of_exc Q x B hxB hB
  have hdown := hs.2.2.2.2.2.2.2.2.2.1
  have hA : A ∈ Q.down B := (mem_down' Q B A).mpr hAB
  rw [hdown] at hA
  simp only [Finset.mem_insert, Finset.mem_singleton] at hA
  rcases hA with h | h
  · subst h; exact ⟨y, z, B, hs⟩
  · exact absurd h hne

theorem XA_of_assoc {A : Fin Q.R} {x y z : Fin n} {B : Fin Q.R} (hs : Assoc Q A x y z B) :
    x ∈ Q.XA A := by
  obtain ⟨hxB, hexc, hAB, -, -, -, -, -, -, hdown, -, -⟩ := hs
  simp only [Member.XA, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨B, hxB, hexc⟩, B, hxB, ?_, hAB.ne⟩
  rw [← mem_down', hdown]; simp

theorem assoc_partners {A : Fin Q.R} {x y z : Fin n} {B : Fin Q.R} (hs : Assoc Q A x y z B) :
    Q.μ A.castSucc y = Q.μ 0 y ∧ Q.μ A.castSucc z = Q.μ 0 z ∧ Q.μ A.succ y = Q.μ 0 z ∧
    Q.μ B.castSucc y = Q.μ 0 z ∧ Q.μ B.castSucc x = Q.μ 0 x ∧
    Q.μ B.succ y = Q.μ 0 x ∧ Q.μ B.succ x = Q.μ 0 z := by
  obtain ⟨hxB, -, hAB, hyz, hyx, -, hpA, hyA, hzA, -, hpB, hgap⟩ := hs
  rw [isFirst_iff] at hxB hyA hzA
  have hy0 : Q.μ A.castSucc y = Q.μ 0 y :=
    man_eq_zero Q y _ (fun k hk => hyA.2 k (lt_of_castSucc hk))
  have hz0 : Q.μ A.castSucc z = Q.μ 0 z :=
    man_eq_zero Q z _ (fun k hk => hzA.2 k (lt_of_castSucc hk))
  have hyS : Q.μ A.succ y = Q.μ 0 z := by rw [swap_eq Q A y z hpA hyz, hz0]
  have hyB : Q.μ B.castSucc y = Q.μ 0 z := by
    rw [man_const Q y A.succ B.castSucc (lt_succ_le hAB)
      (fun k hk1 hk2 => hgap k (lt_of_succ_le hk1) (lt_of_castSucc hk2)), hyS]
  have hxB0 : Q.μ B.castSucc x = Q.μ 0 x :=
    man_eq_zero Q x _ (fun k hk => hxB.2 k (lt_of_castSucc hk))
  have hpB' : Q.participants B = {x, y} := by rw [hpB, Finset.pair_comm]
  refine ⟨hy0, hz0, hyS, hyB, hxB0, ?_, ?_⟩
  · rw [swap_eq Q B y x hpB hyx, hxB0]
  · rw [swap_eq Q B x y hpB' hyx.symm, hyB]

theorem parent_of_assoc {A : Fin Q.R} {x y z : Fin n} {B : Fin Q.R} (hs : Assoc Q A x y z B) :
    Q.IsParent .man x y ∧ Q.IsParent .woman x z := by
  have hP := assoc_partners Q hs
  obtain ⟨hxB, hexc, -, -, hyx, hzx, -, -, -, -, hpB, -⟩ := hs
  have hym : Q.moves .man B y := (mem_participants Q B y).mp (by rw [hpB]; simp)
  refine ⟨⟨⟨B, hxB, hexc⟩, hyx, B, hxB, hym⟩, ⟨⟨B, hxB, hexc⟩, hzx, B, hxB, ?_⟩⟩
  show Q.moves .woman B (Q.μ 0 z)
  rw [← hP.2.2.2.1, moves_woman_iff]
  exact hym

theorem assoc_of_parent_man (A : Fin Q.R) (x w : Fin n) (hP : Q.IsParent .man x w)
    (hw : Q.IsFirst w A) : ∃ z B, Assoc Q A x w z B := by
  obtain ⟨⟨B, hxB, hexc⟩, hwx, i, hxi, hmi⟩ := hP
  have := isFirst_unique Q hxB hxi
  subst this
  obtain ⟨A', y, z, hs⟩ := assoc_of_exc Q x B hxB hexc
  have hpB := hs.2.2.2.2.2.2.2.2.2.2.1
  have hyA := hs.2.2.2.2.2.2.2.1
  have hmem : w ∈ Q.participants B := (mem_participants Q B w).mpr hmi
  rw [hpB] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · subst h
    have := isFirst_unique Q hw hyA
    subst this
    exact ⟨z, B, hs⟩
  · exact absurd h hwx

theorem assoc_of_parent_woman (A : Fin Q.R) (x w : Fin n) (hP : Q.IsParent .woman x w)
    (hw : Q.IsFirst w A) : ∃ y B, Assoc Q A x y w B := by
  obtain ⟨⟨B, hxB, hexc⟩, hwx, i, hxi, hmi⟩ := hP
  have := isFirst_unique Q hxB hxi
  subst this
  obtain ⟨A', y, z, hs⟩ := assoc_of_exc Q x B hxB hexc
  have hpart := assoc_partners Q hs
  have hpB := hs.2.2.2.2.2.2.2.2.2.2.1
  have hzA := hs.2.2.2.2.2.2.2.2.1
  change Q.moves .woman B (Q.μ 0 w) at hmi
  set m := (Q.μ B.castSucc).symm (Q.μ 0 w) with hm
  have hmw : Q.μ B.castSucc m = Q.μ 0 w := by simp [hm]
  rw [← hmw, moves_woman_iff] at hmi
  have hmem : m ∈ Q.participants B := (mem_participants Q B m).mpr hmi
  rw [hpB] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · rw [h, hpart.2.2.2.1] at hmw
    have hwz : z = w := (Q.μ 0).injective hmw
    subst hwz
    have := isFirst_unique Q hw hzA
    subst this
    exact ⟨y, B, hs⟩
  · rw [h, hpart.2.2.2.2.1] at hmw
    exact absurd ((Q.μ 0).injective hmw).symm hwx

theorem assoc_unique_x {A : Fin Q.R} {x1 x2 y z1 z2 : Fin n} {B1 B2 : Fin Q.R}
    (h1 : Assoc Q A x1 y z1 B1) (h2 : Assoc Q A x2 y z2 B2) : x1 = x2 := by
  obtain ⟨-, -, hAB1, -, hyx1, -, -, -, -, -, hpB1, hgap1⟩ := h1
  obtain ⟨-, -, hAB2, -, hyx2, -, -, -, -, -, hpB2, hgap2⟩ := h2
  have hy1 : Q.moves .man B1 y := (mem_participants Q B1 y).mp (by rw [hpB1]; simp)
  have hy2 : Q.moves .man B2 y := (mem_participants Q B2 y).mp (by rw [hpB2]; simp)
  have hB : B1 = B2 := by
    rcases lt_trichotomy B1 B2 with h | h | h
    · exact absurd hy1 (hgap2 B1 hAB1 h)
    · exact h
    · exact absurd hy2 (hgap1 B2 hAB2 h)
  subst hB
  have : x2 ∈ Q.participants B1 := by rw [hpB2]; simp
  rw [hpB1] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h
  · exact absurd h.symm hyx2
  · exact h.symm

theorem assoc_unique_y {A : Fin Q.R} {x y1 y2 z1 z2 : Fin n} {B1 B2 : Fin Q.R}
    (h1 : Assoc Q A x y1 z1 B1) (h2 : Assoc Q A x y2 z2 B2) : y1 = y2 := by
  obtain ⟨hx1, -, -, -, hyx1, -, -, -, -, -, hpB1, -⟩ := h1
  obtain ⟨hx2, -, -, -, hyx2, -, -, -, -, -, hpB2, -⟩ := h2
  have := isFirst_unique Q hx1 hx2
  subst this
  have : y2 ∈ Q.participants B1 := by rw [hpB2]; simp
  rw [hpB1] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h
  · exact h.symm
  · exact absurd h hyx2

theorem down_initial (A : Fin Q.R) (u v : Fin n) (hp : Q.participants A = {u, v})
    (hu : Q.IsFirst u A) (hv : Q.IsFirst v A) : Q.down A = {A} := by
  ext j
  rw [mem_down']
  simp only [Finset.mem_singleton]
  constructor
  · intro hj
    rcases Relation.ReflTransGen.cases_tail hj with h | ⟨c, -, hc, w, hcw, hAw⟩
    · exact h.symm
    · exfalso
      have : w ∈ Q.participants A := (mem_participants Q A w).mpr hAw
      rw [hp] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h
      · subst h; exact ((isFirst_iff Q _ A).mp hu).2 c hc hcw
      · subst h; exact ((isFirst_iff Q _ A).mp hv).2 c hc hcw
  · intro h
    rw [h]
    exact le_rfl' Q A

end assoc

section loss

variable (Q : Member n)

theorem W_sub_one (h : ℕ → ℝ) {d : ℕ} (hd : 1 ≤ d) : W h d - W h (d - 1) = h d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  simp only [W, Nat.add_sub_cancel]
  rw [Finset.sum_Icc_succ_top (by omega)]
  ring

theorem W_sub_two (h : ℕ → ℝ) {d : ℕ} (hd : 2 ≤ d) : W h d - W h (d - 2) = h d + h (d - 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  simp only [W]
  rw [show e + 2 - 2 = e by omega, show e + 2 - 1 = e + 1 by omega,
    show e + 2 = (e + 1) + 1 by omega, Finset.sum_Icc_succ_top (by omega),
    Finset.sum_Icc_succ_top (by omega)]
  ring

theorem W_sub_nonneg (h : ℕ → ℝ) (hnn : ∀ r, 1 ≤ r → 0 ≤ h r) (d k : ℕ) :
    0 ≤ W h d - W h (d - k) := by
  simp only [W, sub_nonneg]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r
    simp only [Finset.mem_Icc]
    omega
  · intro r hr _
    simp only [Finset.mem_Icc] at hr
    exact hnn r hr.1

/-- the loss of the person with label `v` when `↓i` is deleted -/
noncomputable def tm (h : ℕ → ℝ) (s : Sex) (i : Fin Q.R) (v : Fin n) : ℝ :=
  W h (Q.dL s v) - W h (Q.dL s v - (Q.down i ∩ Q.chainOf s (Q.person s v)).card)

theorem pLoss_eq (h : ℕ → ℝ) (s : Sex) (i : Fin Q.R) : Q.pLoss h s i = ∑ v, tm Q h s i v := by
  unfold Member.pLoss Member.Fon tm
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  have e1 : Q.degOn Finset.univ s (Q.person s v) = Q.dL s v := by
    simp [Member.degOn, Member.dL, Member.deg]
  have e2 : Q.degOn (Finset.univ \ Q.down i) s (Q.person s v) =
      Q.dL s v - (Q.down i ∩ Q.chainOf s (Q.person s v)).card := by
    unfold Member.degOn Member.dL Member.deg
    rw [show (Finset.univ \ Q.down i) ∩ Q.chainOf s (Q.person s v) =
      Q.chainOf s (Q.person s v) \ Q.down i by ext; simp; tauto]
    rw [Finset.card_sdiff]
  rw [e1, e2]

theorem tm_nonneg (h : ℕ → ℝ) (hnn : ∀ r, 1 ≤ r → 0 ≤ h r) (s : Sex) (i : Fin Q.R) (v : Fin n) :
    0 ≤ tm Q h s i v := W_sub_nonneg h hnn _ _

theorem pLoss_ge2 (h : ℕ → ℝ) (hnn : ∀ r, 1 ≤ r → 0 ≤ h r) (s : Sex) (i : Fin Q.R)
    (p q : Fin n) (hpq : p ≠ q) : tm Q h s i p + tm Q h s i q ≤ Q.pLoss h s i := by
  rw [pLoss_eq]
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := tm Q h s i)
    (Finset.subset_univ {p, q}) (fun v _ _ => tm_nonneg Q h hnn s i v)
  rwa [Finset.sum_pair hpq] at this

theorem pLoss_ge3 (h : ℕ → ℝ) (hnn : ∀ r, 1 ≤ r → 0 ≤ h r) (s : Sex) (i : Fin Q.R)
    (p q r : Fin n) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    tm Q h s i p + tm Q h s i q + tm Q h s i r ≤ Q.pLoss h s i := by
  rw [pLoss_eq]
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := tm Q h s i)
    (Finset.subset_univ {p, q, r}) (fun v _ _ => tm_nonneg Q h hnn s i v)
  rw [Finset.sum_insert (by simp [hpq, hpr]), Finset.sum_pair hqr] at this
  linarith

theorem card_le_dL (s : Sex) (i : Fin Q.R) (v : Fin n) :
    (Q.down i ∩ Q.chainOf s (Q.person s v)).card ≤ Q.dL s v :=
  Finset.card_le_card Finset.inter_subset_right

theorem tm_one (h : ℕ → ℝ) (s : Sex) (i : Fin Q.R) (v : Fin n)
    (hc : (Q.down i ∩ Q.chainOf s (Q.person s v)).card = 1) :
    tm Q h s i v = h (Q.dL s v) ∧ 1 ≤ Q.dL s v := by
  have hd := card_le_dL Q s i v
  rw [hc] at hd
  refine ⟨?_, hd⟩
  unfold tm
  rw [hc]
  exact W_sub_one h hd

theorem tm_two (h : ℕ → ℝ) (s : Sex) (i : Fin Q.R) (v : Fin n)
    (hc : (Q.down i ∩ Q.chainOf s (Q.person s v)).card = 2) :
    tm Q h s i v = h (Q.dL s v) + h (Q.dL s v - 1) ∧ 2 ≤ Q.dL s v := by
  have hd := card_le_dL Q s i v
  rw [hc] at hd
  refine ⟨?_, hd⟩
  unfold tm
  rw [hc]
  exact W_sub_two h hd

theorem c2 {R : ℕ} {A B : Fin R} {C : Finset (Fin R)} (hAB : A ≠ B) (hA : A ∈ C) (hB : B ∈ C) :
    (({A, B} : Finset (Fin R)) ∩ C).card = 2 := by
  rw [Finset.insert_inter_of_mem hA, Finset.singleton_inter_of_mem hB, Finset.card_pair hAB]

theorem c10 {R : ℕ} {A B : Fin R} {C : Finset (Fin R)} (hA : A ∈ C) (hB : B ∉ C) :
    (({A, B} : Finset (Fin R)) ∩ C).card = 1 := by
  rw [Finset.insert_inter_of_mem hA, Finset.singleton_inter_of_notMem hB]
  simp

theorem c01 {R : ℕ} {A B : Fin R} {C : Finset (Fin R)} (hA : A ∉ C) (hB : B ∈ C) :
    (({A, B} : Finset (Fin R)) ∩ C).card = 1 := by
  rw [Finset.insert_inter_of_notMem hA, Finset.singleton_inter_of_mem hB, Finset.card_singleton]

theorem initial_bound (h : ℕ → ℝ) (hnn : ∀ r, 1 ≤ r → 0 ≤ h r) (A : Fin Q.R) (u v : Fin n)
    (huv : u ≠ v) (hp : Q.participants A = {u, v}) (hu : Q.IsFirst u A) (hv : Q.IsFirst v A)
    (s : Sex) :
    h (Q.dL s u) + h (Q.dL s v) ≤ Q.pLoss h s A ∧ 1 ≤ Q.dL s u ∧ 1 ≤ Q.dL s v := by
  have hd := down_initial Q A u v hp hu hv
  have hmem : ∀ w, Q.IsFirst w A → (Q.down A ∩ Q.chainOf s (Q.person s w)).card = 1 := by
    intro w hw
    obtain ⟨hwV, hwA⟩ := hw
    have := first_mem_chain Q s w hwV
    rw [hwA] at this
    rw [hd, Finset.singleton_inter_of_mem this, Finset.card_singleton]
  obtain ⟨e1, d1⟩ := tm_one Q h s A u (hmem u hu)
  obtain ⟨e2, d2⟩ := tm_one Q h s A v (hmem v hv)
  have := pLoss_ge2 Q h hnn s A u v huv
  rw [e1, e2] at this
  exact ⟨this, d1, d2⟩

theorem succ_le_iff' {R : ℕ} (B k : Fin R) : B.succ ≤ k.castSucc ↔ B < k := by
  rw [Fin.le_def, Fin.lt_def]; simp only [Fin.val_succ, Fin.val_castSucc]; omega

theorem assoc_bound (h : ℕ → ℝ) (hnn : ∀ r, 1 ≤ r → 0 ≤ h r) {A : Fin Q.R} {x y z : Fin n}
    {B : Fin Q.R} (hs : Assoc Q A x y z B) :
    h (Q.dL .man y) + h (Q.dL .man y - 1) + h (Q.dL .man z) + h (Q.dL .man x) ≤
      Q.pLoss h .man B ∧
    h (Q.dL .woman z) + h (Q.dL .woman z - 1) + h (Q.dL .woman y) + h (Q.dL .woman x) ≤
      Q.pLoss h .woman B ∧
    2 ≤ Q.dL .man y ∧ 2 ≤ Q.dL .woman z ∧ 1 ≤ Q.dL .man z ∧ 1 ≤ Q.dL .woman y ∧
    1 ≤ Q.dL .man x ∧ 1 ≤ Q.dL .woman x := by
  have hP := assoc_partners Q hs
  obtain ⟨hxB, -, hAB, hyz, hyx, hzx, hpA, -, -, hdown, hpB, -⟩ := hs
  have hAB' : A ≠ B := hAB.ne
  have hxB' := (isFirst_iff Q x B).mp hxB
  have pm : ∀ i w, Q.participants i = {y, z} ∨ Q.participants i = {y, x} →
      (w ∈ Q.participants i ↔ Q.moves .man i w) := fun i w _ => mem_participants Q i w
  -- men
  have myA : A ∈ Q.chainOf .man (Q.person .man y) :=
    (mem_chainOf Q .man y A).mpr ((pm A y (Or.inl hpA)).mp (by rw [hpA]; simp))
  have myB : B ∈ Q.chainOf .man (Q.person .man y) :=
    (mem_chainOf Q .man y B).mpr ((mem_participants Q B y).mp (by rw [hpB]; simp))
  have mzA : A ∈ Q.chainOf .man (Q.person .man z) :=
    (mem_chainOf Q .man z A).mpr ((mem_participants Q A z).mp (by rw [hpA]; simp))
  have mzB : B ∉ Q.chainOf .man (Q.person .man z) := by
    intro hm
    have := (mem_participants Q B z).mpr ((mem_chainOf Q .man z B).mp hm)
    rw [hpB] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact hyz h.symm
    · exact hzx h
  have mxA : A ∉ Q.chainOf .man (Q.person .man x) := by
    intro hm
    have := (mem_participants Q A x).mpr ((mem_chainOf Q .man x A).mp hm)
    rw [hpA] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact hyx h.symm
    · exact hzx h.symm
  have mxB : B ∈ Q.chainOf .man (Q.person .man x) :=
    (mem_chainOf Q .man x B).mpr hxB'.1
  -- women
  have wzA : A ∈ Q.chainOf .woman (Q.person .woman z) := by
    rw [mem_chainOf]
    show Q.moves .woman A (Q.μ 0 z)
    rw [← hP.2.1, moves_woman_iff]
    exact (mem_participants Q A z).mp (by rw [hpA]; simp)
  have wzB : B ∈ Q.chainOf .woman (Q.person .woman z) := by
    rw [mem_chainOf]
    show Q.moves .woman B (Q.μ 0 z)
    rw [← hP.2.2.2.1, moves_woman_iff]
    exact (mem_participants Q B y).mp (by rw [hpB]; simp)
  have wyA : A ∈ Q.chainOf .woman (Q.person .woman y) := by
    rw [mem_chainOf]
    show Q.moves .woman A (Q.μ 0 y)
    rw [← hP.1, moves_woman_iff]
    exact (mem_participants Q A y).mp (by rw [hpA]; simp)
  have wyB : B ∉ Q.chainOf .woman (Q.person .woman y) := by
    rw [mem_chainOf]
    show ¬ Q.moves .woman B (Q.μ 0 y)
    set m := (Q.μ B.castSucc).symm (Q.μ 0 y) with hm
    have hmw : Q.μ B.castSucc m = Q.μ 0 y := by simp [hm]
    rw [← hmw, moves_woman_iff]
    intro hmv
    have hmem := (mem_participants Q B m).mpr hmv
    rw [hpB] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · rw [h, hP.2.2.2.1] at hmw
      exact hyz ((Q.μ 0).injective hmw).symm
    · rw [h, hP.2.2.2.2.1] at hmw
      exact hyx ((Q.μ 0).injective hmw).symm
  have wxA : A ∉ Q.chainOf .woman (Q.person .woman x) := by
    rw [mem_chainOf]
    show ¬ Q.moves .woman A (Q.μ 0 x)
    have e : Q.μ A.castSucc x = Q.μ 0 x :=
      man_eq_zero Q x _ (fun k hk => hxB'.2 k ((lt_of_castSucc hk).trans hAB))
    rw [← e, moves_woman_iff]
    intro hmv
    exact mxA ((mem_chainOf Q .man x A).mpr hmv)
  have wxB : B ∈ Q.chainOf .woman (Q.person .woman x) := by
    rw [mem_chainOf]
    show Q.moves .woman B (Q.μ 0 x)
    rw [← hP.2.2.2.2.1, moves_woman_iff]
    exact hxB'.1
  obtain ⟨ey, dy⟩ := tm_two Q h .man B y (by rw [hdown]; exact c2 hAB' myA myB)
  obtain ⟨ez, dz⟩ := tm_one Q h .man B z (by rw [hdown]; exact c10 mzA mzB)
  obtain ⟨ex, dx⟩ := tm_one Q h .man B x (by rw [hdown]; exact c01 mxA mxB)
  obtain ⟨fz, gz⟩ := tm_two Q h .woman B z (by rw [hdown]; exact c2 hAB' wzA wzB)
  obtain ⟨fy, gy⟩ := tm_one Q h .woman B y (by rw [hdown]; exact c10 wyA wyB)
  obtain ⟨fx, gx⟩ := tm_one Q h .woman B x (by rw [hdown]; exact c01 wxA wxB)
  have b1 := pLoss_ge3 Q h hnn .man B y z x hyz hyx hzx
  have b2 := pLoss_ge3 Q h hnn .woman B z y x hyz.symm hzx hyx
  rw [ey, ez, ex] at b1
  rw [fz, fy, fx] at b2
  exact ⟨b1, b2, dy, gz, dz, gy, dx, gx⟩

theorem assoc_deg {A : Fin Q.R} {x y z : Fin n} {B : Fin Q.R} (hs : Assoc Q A x y z B) :
    (Q.dL .man x = 1 ↔ Q.dL .woman z = 2) ∧ (Q.dL .woman x = 1 ↔ Q.dL .man y = 2) := by
  have hP := assoc_partners Q hs
  obtain ⟨hxB, -, hAB, hyz, hyx, hzx, hpA, hyA, hzA, -, hpB, hgap⟩ := hs
  have hAB' : A ≠ B := hAB.ne
  rw [isFirst_iff] at hxB hyA hzA
  have hym : ∀ i, Q.participants i = {y, x} → Q.moves .man i y := fun i hi =>
    (mem_participants Q i y).mp (by rw [hi]; simp)
  -- men's chain of x
  have hx1 : Q.dL .man x = 1 ↔ ∀ k, B < k → ¬ Q.moves .man k x := by
    have := card_chain_iff (Q.chainOf .man x) {B} B
      (by intro k hk; rw [Finset.mem_singleton] at hk; subst hk
          exact (mem_chainOf Q .man x _).mpr hxB.1)
      (by intro k hk; rw [Finset.mem_singleton] at hk; rw [hk])
      (by
        intro k hk hkS
        rw [mem_chainOf] at hk
        rw [Finset.mem_singleton] at hkS
        exact lt_of_le_of_ne (not_lt.mp fun h => hxB.2 k h hk) (Ne.symm hkS))
    rw [Finset.card_singleton] at this
    show (Q.chainOf .man x).card = 1 ↔ _
    rw [this]
    simp only [mem_chainOf]
  -- women's chain of `μ₀ x`
  have hwx1 : Q.dL .woman x = 1 ↔ ∀ k, B < k → ¬ Q.moves .woman k (Q.μ 0 x) := by
    have := card_chain_iff (Q.chainOf .woman (Q.μ 0 x)) {B} B
      (by intro k hk; rw [Finset.mem_singleton] at hk; subst hk
          rw [mem_chainOf, ← hP.2.2.2.2.1, moves_woman_iff]; exact hxB.1)
      (by intro k hk; rw [Finset.mem_singleton] at hk; rw [hk])
      (by
        intro k hk hkS
        rw [mem_chainOf] at hk
        rw [Finset.mem_singleton] at hkS
        refine lt_of_le_of_ne (not_lt.mp fun h => ?_) (Ne.symm hkS)
        have e : Q.μ k.castSucc x = Q.μ 0 x :=
          man_eq_zero Q x _ (fun k' hk' => hxB.2 k' ((lt_of_castSucc hk').trans h))
        rw [← e, moves_woman_iff] at hk
        exact hxB.2 k h hk)
    rw [Finset.card_singleton] at this
    show (Q.chainOf .woman (Q.μ 0 x)).card = 1 ↔ _
    rw [this]
    simp only [mem_chainOf]
  -- men's chain of y
  have hy2 : Q.dL .man y = 2 ↔ ∀ k, B < k → ¬ Q.moves .man k y := by
    have := card_chain_iff (Q.chainOf .man y) {A, B} B
      (by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rw [mem_chainOf]
        rcases hk with rfl | rfl
        · exact hyA.1
        · exact hym _ hpB)
      (by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact hAB.le
        · exact le_refl _)
      (by
        intro k hk hkS
        rw [mem_chainOf] at hk
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hkS
        refine lt_of_le_of_ne (not_lt.mp fun h => ?_) (Ne.symm hkS.2)
        rcases lt_or_gt_of_ne hkS.1 with h' | h'
        · exact hyA.2 k h' hk
        · exact hgap k h' h hk)
    rw [Finset.card_pair hAB'] at this
    show (Q.chainOf .man y).card = 2 ↔ _
    rw [this]
    simp only [mem_chainOf]
  -- women's chain of `μ₀ z`
  have hz2 : Q.dL .woman z = 2 ↔ ∀ k, B < k → ¬ Q.moves .woman k (Q.μ 0 z) := by
    have := card_chain_iff (Q.chainOf .woman (Q.μ 0 z)) {A, B} B
      (by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rw [mem_chainOf]
        rcases hk with rfl | rfl
        · rw [← hP.2.1, moves_woman_iff]
          exact (mem_participants Q _ z).mp (by rw [hpA]; simp)
        · rw [← hP.2.2.2.1, moves_woman_iff]
          exact hym _ hpB)
      (by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact hAB.le
        · exact le_refl _)
      (by
        intro k hk hkS
        rw [mem_chainOf] at hk
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hkS
        refine lt_of_le_of_ne (not_lt.mp fun h => ?_) (Ne.symm hkS.2)
        rcases lt_or_gt_of_ne hkS.1 with h' | h'
        · have e : Q.μ k.castSucc z = Q.μ 0 z :=
            man_eq_zero Q z _ (fun k' hk' => hzA.2 k' ((lt_of_castSucc hk').trans h'))
          rw [← e, moves_woman_iff] at hk
          exact hzA.2 k h' hk
        · have e : Q.μ k.castSucc y = Q.μ 0 z := by
            rw [man_const Q y A.succ k.castSucc (lt_succ_le h')
              (fun k' hk1 hk2 => hgap k' (lt_of_succ_le hk1) ((lt_of_castSucc hk2).trans h)),
              hP.2.2.1]
          rw [← e, moves_woman_iff] at hk
          exact hgap k h' h hk)
    rw [Finset.card_pair hAB'] at this
    show (Q.chainOf .woman (Q.μ 0 z)).card = 2 ↔ _
    rw [this]
    simp only [mem_chainOf]
  have pr1 := pair_moves Q x B.succ
  have pr2 := pair_moves Q y B.succ
  rw [hP.2.2.2.2.2.2] at pr1
  rw [hP.2.2.2.2.2.1] at pr2
  simp only [succ_le_iff'] at pr1 pr2
  constructor
  · rw [hx1, hz2]
    constructor
    · intro h1 k hk hm
      obtain ⟨k', hk', hm'⟩ := pr1.mpr ⟨k, hk, hm⟩
      exact h1 k' hk' hm'
    · intro h1 k hk hm
      obtain ⟨k', hk', hm'⟩ := pr1.mp ⟨k, hk, hm⟩
      exact h1 k' hk' hm'
  · rw [hwx1, hy2]
    constructor
    · intro h1 k hk hm
      obtain ⟨k', hk', hm'⟩ := pr2.mp ⟨k, hk, hm⟩
      exact h1 k' hk' hm'
    · intro h1 k hk hm
      obtain ⟨k', hk', hm'⟩ := pr2.mpr ⟨k, hk, hm⟩
      exact h1 k' hk' hm'

end loss

end Dev.L62

end StableCount
end

section
namespace StableCount

open StableMatching

namespace Dev.L62

/-! ### Analysis: `λ`, admissibility and the per-sex bounds (20) -/

theorem ose_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-t) := by
  have : Real.exp (-t) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  linarith

theorem lam_anti' {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : lam b ≤ lam a := by
  unfold lam
  have h1 := ose_pos ha
  have h2 : 1 - Real.exp (-a) ≤ 1 - Real.exp (-b) := by
    have : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have := Real.log_le_log h1 h2
  linarith

theorem lam_convex : ConvexOn ℝ (Set.Ioi 0) lam := by
  refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [Set.mem_Ioi] at hx hy
  simp only [smul_eq_mul]
  have hA := ose_pos hx
  have hB := ose_pos hy
  have hlog := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.mpr hA) (Set.mem_Ioi.mpr hB)
    ha hb hab
  simp only [smul_eq_mul] at hlog
  have hexp := convexOn_exp.2 (Set.mem_univ (-x)) (Set.mem_univ (-y)) ha hb hab
  simp only [smul_eq_mul] at hexp
  have e : a * -x + b * -y = -(a * x + b * y) := by ring
  rw [e] at hexp
  have hpos : 0 < a * (1 - Real.exp (-x)) + b * (1 - Real.exp (-y)) := by
    rcases ha.lt_or_eq with ha' | ha'
    · have := mul_pos ha' hA
      have := mul_nonneg hb hB.le
      linarith
    · subst ha'
      have : b = 1 := by linarith
      subst this
      simpa using hB
  have e2 : a * (1 - Real.exp (-x)) + b * (1 - Real.exp (-y)) =
      (a + b) - (a * Real.exp (-x) + b * Real.exp (-y)) := by ring
  have h2 : a * (1 - Real.exp (-x)) + b * (1 - Real.exp (-y)) ≤
      1 - Real.exp (-(a * x + b * y)) := by
    rw [e2, hab]; linarith
  have := Real.log_le_log hpos h2
  unfold lam
  linarith

theorem lam_mid {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    2 * lam ((p + q) / 2) ≤ lam p + lam q := by
  have := lam_convex.2 (Set.mem_Ioi.mpr hp) (Set.mem_Ioi.mpr hq)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at this
  rw [show 1 / 2 * p + 1 / 2 * q = (p + q) / 2 by ring] at this
  linarith

/-- convexity between two points, written with the two gaps `α, β` -/
theorem convex_interp {P2 α β : ℝ} (hP2 : 0 < P2) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (α + β) * lam (P2 + α) ≤ α * lam (P2 + α + β) + β * lam P2 := by
  rcases (add_nonneg hα hβ).lt_or_eq with hD | hD
  · have ha : 0 ≤ α / (α + β) := div_nonneg hα hD.le
    have hb : 0 ≤ β / (α + β) := div_nonneg hβ hD.le
    have hab : α / (α + β) + β / (α + β) = 1 := by field_simp
    have hc := lam_convex.2 (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < P2 + α + β))
      (Set.mem_Ioi.mpr hP2) ha hb hab
    simp only [smul_eq_mul] at hc
    have e : α / (α + β) * (P2 + α + β) + β / (α + β) * P2 = P2 + α := by
      field_simp; ring
    rw [e] at hc
    have := mul_le_mul_of_nonneg_left hc hD.le
    have e2 : (α + β) * (α / (α + β) * lam (P2 + α + β) + β / (α + β) * lam P2) =
        α * lam (P2 + α + β) + β * lam P2 := by
      field_simp
    linarith
  · have h1 : α = 0 := by linarith
    have h2 : β = 0 := by linarith
    subst h1 h2
    simp

theorem comb {α β L1 L2 M1 M2 LP LQ T : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (i1 : (α + β) * LP ≤ α * L1 + β * L2) (i2 : (α + β) * LQ ≤ β * M1 + α * M2)
    (b1 : L1 + M2 ≤ T) (b2 : L2 + M1 ≤ T) (hdeg : β = 0 → LP = L1 ∧ LQ = M2) :
    LP + LQ ≤ T := by
  rcases (add_nonneg hα hβ).lt_or_eq with hD | hD
  · have k1 := mul_le_mul_of_nonneg_left b1 hα
    have k2 := mul_le_mul_of_nonneg_left b2 hβ
    have : (α + β) * (LP + LQ) ≤ (α + β) * T := by nlinarith
    exact le_of_mul_le_mul_left this hD
  · obtain ⟨e1, e2⟩ := hdeg (by linarith)
    rw [e1, e2]; exact b1

section adm

variable {h : ℕ → ℝ}

theorem hpos (hh : IsAdmissible h) {d : ℕ} (hd : 1 ≤ d) : 0 < h d := hh.1 d hd

theorem hanti (hh : IsAdmissible h) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : h j ≤ h i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ j hij ih => exact (hh.2.1 j (by omega)).trans ih

theorem Hsum_one (h : ℕ → ℝ) : Hsum h 1 = 2 * h 1 := by
  unfold Hsum
  rw [Finset.Icc_self, Finset.sum_singleton]
  norm_num

theorem lam_log2 : lam (Real.log 2) = Real.log 2 := by
  unfold lam
  rw [Real.exp_neg, Real.exp_log (by norm_num)]
  rw [show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num, Real.log_inv]
  ring

/-- Lemma 5.6 -/
theorem L56 (hh : IsAdmissible h) {d : ℕ} (hd : 1 ≤ d) :
    lam (2 * h d) ≤ Hsum h d + (if 2 ≤ d then h 2 else 0) := by
  rcases (show d = 1 ∨ 2 ≤ d by omega) with rfl | hd2
  · rw [if_neg (by norm_num), Hsum_one, add_zero]
    have h1 : Real.log 2 ≤ 2 * h 1 := hh.2.2.1
    have := lam_anti' (Real.log_pos (by norm_num)) h1
    rw [lam_log2] at this
    linarith
  · rw [if_pos hd2]
    exact hh.2.2.2.1 d hd2

/-- Lemma 6.1 (ii), for one `c` -/
theorem L61ii (hh : IsAdmissible h) {c : ℕ} (hc : 1 ≤ c) :
    lam (h 1 + h 2 + h c) - Aval h c ≤ -h 1 - h 2 := by
  have p1 := hpos hh (le_refl 1)
  have p2 := hpos hh (by norm_num : 1 ≤ 2)
  have pc := hpos hh hc
  have h21 : h 2 ≤ h 1 := hanti hh le_rfl (by norm_num)
  rcases (show c = 1 ∨ 2 ≤ c by omega) with rfl | hc2
  · rw [Aval, if_pos rfl]
    have a := lam_anti' (by positivity : 0 < 2 * h 1) (by linarith : 2 * h 1 ≤ h 1 + h 2 + h 1)
    have b := L56 hh (le_refl 1)
    rw [if_neg (by norm_num), Hsum_one] at b
    linarith
  · rw [Aval, if_neg (by omega)]
    have hc1 : h c ≤ h 1 := hanti hh le_rfl hc
    have a := lam_anti' (by positivity : 0 < 2 * h c) (by linarith : 2 * h c ≤ h 1 + h 2 + h c)
    have b : lam (2 * h c) ≤ Hsum h c + h 2 := hh.2.2.2.1 c hc2
    linarith

/-- Lemma 6.1 (i), for one `c` -/
theorem L61i (hh : IsAdmissible h) {a c : ℕ} (ha : 2 ≤ a) (hc : 1 ≤ c) :
    lam (h (a - 1) + 2 * h a + h c) - Aval h c ≤
      Hsum h a - lam (2 * h a) - (if a = 2 then h 1 else 0) := by
  rcases (show a = 2 ∨ 3 ≤ a by omega) with rfl | ha3
  · rw [if_pos rfl, show (2 : ℕ) - 1 = 1 from rfl]
    have p1 := hpos hh (le_refl 1)
    have p2 := hpos hh (by norm_num : 1 ≤ 2)
    have pc := hpos hh hc
    have m := lam_anti' (by positivity : 0 < h 1 + h 2 + h c)
      (by linarith : h 1 + h 2 + h c ≤ h 1 + 2 * h 2 + h c)
    have i := L61ii hh hc
    have s := L56 hh (by norm_num : 1 ≤ 2)
    rw [if_pos le_rfl] at s
    linarith
  · rw [if_neg (by omega)]
    have := hh.2.2.2.2.1 a c ha3 hc
    linarith

theorem Aval_eq {c : ℕ} (hc : 1 ≤ c) :
    Aval h c = Hsum h c + h 1 + 2 * (if 2 ≤ c then h 2 else 0) + (if c = 1 then h 1 else 0) := by
  rcases (show c = 1 ∨ 2 ≤ c by omega) with rfl | hc2
  · rw [Aval, if_pos rfl, if_neg (by norm_num), if_pos rfl, Hsum_one]; ring
  · rw [Aval, if_neg (by omega), if_pos hc2, if_neg (by omega)]; ring

theorem two_lam_pA (hh : IsAdmissible h) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {pA : ℝ}
    (hpA : h a + h b ≤ pA) : 2 * lam pA ≤ lam (2 * h a) + lam (2 * h b) := by
  have pa := hpos hh ha
  have pb := hpos hh hb
  have m := lam_anti' (by positivity : 0 < h a + h b) hpA
  have c := lam_mid (by positivity : 0 < 2 * h a) (by positivity : 0 < 2 * h b)
  rw [show (2 * h a + 2 * h b) / 2 = h a + h b by ring] at c
  linarith

/-- (20) when `X_A = ∅` -/
theorem case0 (hh : IsAdmissible h) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {pA : ℝ}
    (hpA : h a + h b ≤ pA) :
    2 * lam pA ≤ (Hsum h a + (if 2 ≤ a then h 2 else 0)) + (Hsum h b + (if 2 ≤ b then h 2 else 0)) := by
  have := two_lam_pA hh ha hb hpA
  have s1 := L56 hh ha
  have s2 := L56 hh hb
  linarith

/-- (20) when `X_A = {x}`, `x` associated with the person of degree `a` -/
theorem case1 (hh : IsAdmissible h) {a b c : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    {pA pB : ℝ} (hpA : h a + h b ≤ pA) (hpB : h a + h (a - 1) + h b + h c ≤ pB) :
    2 * lam pA + lam pB ≤
      Hsum h a + (Hsum h b + (if 2 ≤ b then h 2 else 0)) + Aval h c - (if a = 2 then h 1 else 0) := by
  have t := two_lam_pA hh (by omega) hb hpA
  have pa := hpos hh (show 1 ≤ a by omega)
  have pa1 := hpos hh (show 1 ≤ a - 1 by omega)
  have pb := hpos hh hb
  have pc := hpos hh hc
  have p1 := hpos hh (le_refl 1)
  have p2 := hpos hh (by norm_num : 1 ≤ 2)
  have sb := L56 hh hb
  rcases (show a = 2 ∨ 3 ≤ a by omega) with rfl | ha3
  · rw [if_pos rfl]
    rw [show (2 : ℕ) - 1 = 1 from rfl] at hpB
    have m := lam_anti' (by positivity : 0 < h 1 + h 2 + h c)
      (by linarith : h 1 + h 2 + h c ≤ pB)
    have i := L61ii hh hc
    have s := L56 hh (by norm_num : 1 ≤ 2)
    rw [if_pos le_rfl] at s
    linarith
  · rw [if_neg (show ¬ a = 2 by omega)]
    rcases le_or_gt b a with hba | hab
    · have hhb : h a ≤ h b := hanti hh hb hba
      have m := lam_anti' (by positivity : 0 < h (a - 1) + 2 * h a + h c)
        (by linarith : h (a - 1) + 2 * h a + h c ≤ pB)
      have := hh.2.2.2.2.1 a c ha3 hc
      linarith
    · have hb3 : 3 ≤ b := by omega
      have hhb : h b ≤ h a := hanti hh (by omega) hab.le
      have hhb1 : h (b - 1) ≤ h (a - 1) := hanti hh (by omega) (by omega)
      have pb1 := hpos hh (show 1 ≤ b - 1 by omega)
      have m := lam_anti' (by positivity : 0 < h (b - 1) + 2 * h b + h c)
        (by linarith : h (b - 1) + 2 * h b + h c ≤ pB)
      have := hh.2.2.2.2.1 b c hb3 hc
      have sa := L56 hh (show 1 ≤ a by omega)
      rw [if_pos (show 2 ≤ a by omega)] at sa
      rw [if_pos (show 2 ≤ b by omega)]
      linarith

theorem case2_le (hh : IsAdmissible h) {a b c1 c2 : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hc1 : 1 ≤ c1)
    (hc2 : 1 ≤ c2) {pA pB1 pB2 : ℝ} (hpA : h a + h b ≤ pA)
    (hpB1 : h a + h (a - 1) + h b + h c1 ≤ pB1) (hpB2 : h b + h (b - 1) + h a + h c2 ≤ pB2) :
    2 * lam pA + lam pB1 + lam pB2 ≤ Hsum h a + Hsum h b + Aval h c1 + Aval h c2 -
      (if a = 2 then h 1 else 0) - (if b = 2 then h 1 else 0) := by
  have hb : 2 ≤ b := ha.trans hab
  have t := two_lam_pA hh (by omega) (by omega) hpA
  have pa := hpos hh (show 1 ≤ a by omega)
  have pa1 := hpos hh (show 1 ≤ a - 1 by omega)
  have pb := hpos hh (show 1 ≤ b by omega)
  have pb1 := hpos hh (show 1 ≤ b - 1 by omega)
  have pc1 := hpos hh hc1
  have pc2 := hpos hh hc2
  have hhb : h b ≤ h a := hanti hh (by omega) hab
  have hhb1 : h (b - 1) ≤ h (a - 1) := hanti hh (by omega) (by omega)
  have hα : 0 ≤ (h (a - 1) - h (b - 1)) + (h a - h b) := by linarith
  have hβ : 0 ≤ h a - h b := by linarith
  have i1 := convex_interp (P2 := h (b - 1) + 2 * h b + h c1) (by positivity) hα hβ
  have i2 := convex_interp (P2 := h (b - 1) + 2 * h b + h c2) (by positivity) hβ hα
  rw [add_comm (h a - h b)] at i2
  have r1 := L61i hh ha hc1
  have r2 := L61i hh hb hc1
  have r3 := L61i hh ha hc2
  have r4 := L61i hh hb hc2
  have e1 : lam (h (b - 1) + 2 * h b + h c1 + (h (a - 1) - h (b - 1) + (h a - h b)) +
      (h a - h b)) = lam (h (a - 1) + 2 * h a + h c1) := by congr 1; ring
  have e2 : lam (h (b - 1) + 2 * h b + h c2 + (h a - h b) + (h (a - 1) - h (b - 1) +
      (h a - h b))) = lam (h (a - 1) + 2 * h a + h c2) := by congr 1; ring
  rw [e1] at i1
  rw [e2] at i2
  have key := comb hα hβ i1 i2 (T := Hsum h a - lam (2 * h a) - (if a = 2 then h 1 else 0) +
      (Hsum h b - lam (2 * h b) - (if b = 2 then h 1 else 0)) + Aval h c1 + Aval h c2)
    (by linarith) (by linarith) (by
      intro h0
      constructor
      · congr 1; linarith
      · congr 1; linarith)
  have m1 := lam_anti' (by positivity : 0 < h (b - 1) + 2 * h b + h c1 +
      (h (a - 1) - h (b - 1) + (h a - h b))) (by linarith :
      h (b - 1) + 2 * h b + h c1 + (h (a - 1) - h (b - 1) + (h a - h b)) ≤ pB1)
  have m2 := lam_anti' (by positivity : 0 < h (b - 1) + 2 * h b + h c2 + (h a - h b))
    (by linarith : h (b - 1) + 2 * h b + h c2 + (h a - h b) ≤ pB2)
  linarith

/-- (20) when `|X_A| = 2` -/
theorem case2 (hh : IsAdmissible h) {a b c1 c2 : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc1 : 1 ≤ c1)
    (hc2 : 1 ≤ c2) {pA pB1 pB2 : ℝ} (hpA : h a + h b ≤ pA)
    (hpB1 : h a + h (a - 1) + h b + h c1 ≤ pB1) (hpB2 : h b + h (b - 1) + h a + h c2 ≤ pB2) :
    2 * lam pA + lam pB1 + lam pB2 ≤ Hsum h a + Hsum h b + Aval h c1 + Aval h c2 -
      (if a = 2 then h 1 else 0) - (if b = 2 then h 1 else 0) := by
  rcases le_total a b with hab | hba
  · exact case2_le hh ha hab hc1 hc2 hpA hpB1 hpB2
  · have := case2_le hh hb hba hc2 hc1 (pA := pA) (by linarith) hpB2 hpB1
    linarith

end adm


/-! ### Assembly -/

section final

variable {n : ℕ} (Q : Member n)

theorem pair_cases {u v y z : Fin n} (huv : u ≠ v) (hyz : y ≠ z)
    (h : ({u, v} : Finset (Fin n)) = {y, z}) : (y = u ∧ z = v) ∨ (y = v ∧ z = u) := by
  have hy : y ∈ ({u, v} : Finset (Fin n)) := by rw [h]; simp
  have hz : z ∈ ({u, v} : Finset (Fin n)) := by rw [h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy hz
  rcases hy with h1 | h1 <;> rcases hz with h2 | h2
  · exact absurd (h1.trans h2.symm) hyz
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hyz

theorem fg_eq {A : Fin Q.R} {u v : Fin n} (hp : Q.participants A = {u, v})
    (hu : Q.IsFirst u A) (hv : Q.IsFirst v A) : Q.firstGroup A = {u, v} := by
  ext w
  simp only [Member.firstGroup, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hw
    rw [← hp, mem_participants]
    exact ((isFirst_iff Q w A).mp hw).1
  · intro hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with h | h
    · rw [h]; exact hu
    · rw [h]; exact hv

theorem beta_x (h : ℕ → ℝ) {A : Fin Q.R} {x : Fin n} (hx : x ∈ Q.XA A) (s : Sex) :
    Q.beta h s x = Hsum h (Q.dL s x) + h 1 + (if 2 ≤ Q.dL s x then h 2 else 0) := by
  obtain ⟨y, z, B, hs⟩ := assoc_of_XA Q A x hx
  have hxB := hs.1
  have hexc := hs.2.1
  have c1 : ¬ ∃ i, Q.IsFirst x i ∧ Q.IsOrdinary i := by
    rintro ⟨i, hi, hord⟩
    have := isFirst_unique Q hi hxB
    subst this
    exact hord.2.2 hexc
  have c2 : Q.IsExceptional x := ⟨B, hxB, hexc⟩
  simp only [Member.beta]
  rw [if_neg c1, if_pos c2]

open Classical in
theorem beta_w (h : ℕ → ℝ) {A : Fin Q.R} (hA : Q.IsInitialSwap A) {u v w : Fin n} (huv : u ≠ v)
    (hp : Q.participants A = {u, v}) (hu : Q.IsFirst u A) (hv : Q.IsFirst v A)
    (hw : Q.IsFirst w A) (s : Sex) :
    Q.beta h s w = Hsum h (Q.dL s w) +
      (if ∃ x, Q.IsParent s x w then 0 else (if 2 ≤ Q.dL s w then h 2 else 0)) := by
  have c1 : ¬ ∃ i, Q.IsFirst w i ∧ Q.IsOrdinary i := by
    rintro ⟨i, hi, hord⟩
    have := isFirst_unique Q hi hw
    subst this
    exact hord.2.1 hA
  have c2 : ¬ Q.IsExceptional w := by
    rintro ⟨i, hi, hexc⟩
    have := isFirst_unique Q hi hw
    subst this
    have h1 := hexc.1
    rw [fg_eq Q hp hu hv, Finset.card_pair huv] at h1
    exact absurd h1 (by norm_num)
  simp only [Member.beta]
  rw [if_neg c1, if_neg c2]
  split_ifs <;> ring

theorem parent_man_iff {A : Fin Q.R} {u v : Fin n} (huv : u ≠ v)
    (hp : Q.participants A = {u, v}) (hu : Q.IsFirst u A) :
    (∃ x, Q.IsParent .man x u) ↔ ∃ x B, Assoc Q A x u v B := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨z, B, hs⟩ := assoc_of_parent_man Q A x u hx hu
    rcases pair_cases huv hs.2.2.2.1 (hp.symm.trans hs.2.2.2.2.2.2.1) with ⟨-, h2⟩ | ⟨h1, -⟩
    · rw [h2] at hs; exact ⟨x, B, hs⟩
    · exact absurd h1 huv
  · rintro ⟨x, B, hs⟩
    exact ⟨x, (parent_of_assoc Q hs).1⟩

theorem parent_woman_iff {A : Fin Q.R} {u v : Fin n} (huv : u ≠ v)
    (hp : Q.participants A = {u, v}) (hu : Q.IsFirst u A) :
    (∃ x, Q.IsParent .woman x u) ↔ ∃ x B, Assoc Q A x v u B := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, B, hs⟩ := assoc_of_parent_woman Q A x u hx hu
    rcases pair_cases huv hs.2.2.2.1 (hp.symm.trans hs.2.2.2.2.2.2.1) with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1 hs.2.2.2.1
    · rw [h1] at hs; exact ⟨x, B, hs⟩
  · rintro ⟨x, B, hs⟩
    exact ⟨x, (parent_of_assoc Q hs).2⟩

theorem atFirst_eq {x : Fin n} {B : Fin Q.R} (hx : Q.IsFirst x B) (f : Fin Q.R → ℝ) :
    Q.atFirst f x = f B := by
  obtain ⟨hv, rfl⟩ := hx
  simp [Member.atFirst, hv]

theorem DStar_eq (h : ℕ → ℝ) {A : Fin Q.R} {u v : Fin n} (huv : u ≠ v)
    (hp : Q.participants A = {u, v}) (hu : Q.IsFirst u A) (hv : Q.IsFirst v A) :
    Q.DStar h A = 2 * lam (Q.pStar h A) +
      ∑ x ∈ Q.XA A, Q.atFirst (fun i => lam (Q.pStar h i)) x -
      (1 / 2) * ((Q.beta h .man u + Q.beta h .woman u) + (Q.beta h .man v + Q.beta h .woman v)) -
      (1 / 2) * ∑ x ∈ Q.XA A, (Q.beta h .man x + Q.beta h .woman x) := by
  have hdisj : Disjoint (Q.firstGroup A) (Q.XA A) := by
    rw [Finset.disjoint_left]
    intro w hw hwX
    simp only [Member.firstGroup, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨y, z, B, hs⟩ := assoc_of_XA Q A w hwX
    have := isFirst_unique Q hw hs.1
    exact hs.2.2.1.ne this
  unfold Member.DStar Member.KA
  rw [Finset.sum_union hdisj, fg_eq Q hp hu hv, Finset.sum_pair huv]
  ring

theorem hN (h : ℕ → ℝ) (A : Fin Q.R) (s : Sex) :
    h 2 * (Q.NA s A : ℝ) = ∑ x ∈ Q.XA A, (if 2 ≤ Q.dL s x then h 2 else 0) := by
  unfold Member.NA
  rw [Finset.card_filter]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem lam_star (h : ℕ → ℝ) (i : Fin Q.R) (hm : 0 < Q.pLoss h .man i)
    (hw : 0 < Q.pLoss h .woman i) :
    2 * lam (Q.pStar h i) ≤ lam (Q.pLoss h .man i) + lam (Q.pLoss h .woman i) := by
  unfold Member.pStar
  exact lam_mid hm hw

theorem ite_iff {P P' : Prop} [Decidable P] [Decidable P'] (hP : P ↔ P') (a : ℝ) :
    (if P then a else 0) = (if P' then a else 0) := by
  by_cases h1 : P
  · rw [if_pos h1, if_pos (hP.mp h1)]
  · rw [if_neg h1, if_neg (fun h2 => h1 (hP.mpr h2))]

theorem final0 (h : ℕ → ℝ) (hh : IsAdmissible h) {A : Fin Q.R} (hA : Q.IsInitialSwap A)
    {u v : Fin n} (huv : u ≠ v) (hp : Q.participants A = {u, v}) (hu : Q.IsFirst u A)
    (hv : Q.IsFirst v A) (hU : ¬ ∃ x B, Assoc Q A x u v B) (hV : ¬ ∃ x B, Assoc Q A x v u B) :
    Q.DStar h A ≤ (h 2 / 2) * ((Q.NA .man A : ℝ) + (Q.NA .woman A : ℝ)) := by
  have hnn : ∀ r, 1 ≤ r → 0 ≤ h r := fun r hr => (hpos hh hr).le
  have hp' : Q.participants A = {v, u} := by rw [hp, Finset.pair_comm]
  have hX : Q.XA A = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨y, z, B, hs⟩ := assoc_of_XA Q A x hx
    rcases pair_cases huv hs.2.2.2.1 (hp.symm.trans hs.2.2.2.2.2.2.1) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at hs; exact hU ⟨x, B, hs⟩
    · rw [h1, h2] at hs; exact hV ⟨x, B, hs⟩
  have bmu := beta_w Q h hA huv hp hu hv hu .man
  have bwu := beta_w Q h hA huv hp hu hv hu .woman
  have bmv := beta_w Q h hA huv hp hu hv hv .man
  have bwv := beta_w Q h hA huv hp hu hv hv .woman
  rw [if_neg (by rw [parent_man_iff Q huv hp hu]; exact hU)] at bmu
  rw [if_neg (by rw [parent_woman_iff Q huv hp hu]; exact hV)] at bwu
  rw [if_neg (by rw [parent_man_iff Q huv.symm hp' hv]; exact hV)] at bmv
  rw [if_neg (by rw [parent_woman_iff Q huv.symm hp' hv]; exact hU)] at bwv
  have hNm := hN Q h A .man
  have hNw := hN Q h A .woman
  rw [hX, Finset.sum_empty] at hNm hNw
  rw [DStar_eq Q h huv hp hu hv, hX, Finset.sum_empty, Finset.sum_empty]
  obtain ⟨bm, dmu, dmv⟩ := initial_bound Q h hnn A u v huv hp hu hv .man
  obtain ⟨bw, dwu, dwv⟩ := initial_bound Q h hnn A u v huv hp hu hv .woman
  have cm := case0 hh dmu dmv bm
  have cw := case0 hh dwu dwv bw
  have ls := lam_star Q h A (by linarith [hpos hh dmu, hpos hh dmv])
    (by linarith [hpos hh dwu, hpos hh dwv])
  linarith

theorem final1 (h : ℕ → ℝ) (hh : IsAdmissible h) {A : Fin Q.R} (hA : Q.IsInitialSwap A)
    {u v : Fin n} (huv : u ≠ v) (hp : Q.participants A = {u, v}) (hu : Q.IsFirst u A)
    (hv : Q.IsFirst v A) (x : Fin n) (B : Fin Q.R) (hs : Assoc Q A x u v B)
    (hV : ¬ ∃ x B, Assoc Q A x v u B) :
    Q.DStar h A ≤ (h 2 / 2) * ((Q.NA .man A : ℝ) + (Q.NA .woman A : ℝ)) := by
  have hnn : ∀ r, 1 ≤ r → 0 ≤ h r := fun r hr => (hpos hh hr).le
  have hp' : Q.participants A = {v, u} := by rw [hp, Finset.pair_comm]
  have hX : Q.XA A = {x} := by
    ext x'
    rw [Finset.mem_singleton]
    constructor
    · intro hx
      obtain ⟨y, z, B', hs'⟩ := assoc_of_XA Q A x' hx
      rcases pair_cases huv hs'.2.2.2.1 (hp.symm.trans hs'.2.2.2.2.2.2.1) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at hs'; exact assoc_unique_x Q hs' hs
      · rw [h1, h2] at hs'; exact absurd ⟨x', B', hs'⟩ hV
    · intro hx; rw [hx]; exact XA_of_assoc Q hs
  have hxX : x ∈ Q.XA A := by rw [hX]; simp
  have bmu := beta_w Q h hA huv hp hu hv hu .man
  have bwu := beta_w Q h hA huv hp hu hv hu .woman
  have bmv := beta_w Q h hA huv hp hu hv hv .man
  have bwv := beta_w Q h hA huv hp hu hv hv .woman
  rw [if_pos (by rw [parent_man_iff Q huv hp hu]; exact ⟨x, B, hs⟩)] at bmu
  rw [if_neg (by rw [parent_woman_iff Q huv hp hu]; exact hV)] at bwu
  rw [if_neg (by rw [parent_man_iff Q huv.symm hp' hv]; exact hV)] at bmv
  rw [if_pos (by rw [parent_woman_iff Q huv.symm hp' hv]; exact ⟨x, B, hs⟩)] at bwv
  have bmx := beta_x Q h hxX .man
  have bwx := beta_x Q h hxX .woman
  have hNm := hN Q h A .man
  have hNw := hN Q h A .woman
  rw [hX, Finset.sum_singleton] at hNm hNw
  rw [DStar_eq Q h huv hp hu hv, hX, Finset.sum_singleton, Finset.sum_singleton,
    atFirst_eq Q hs.1]
  obtain ⟨bm, dmu, dmv⟩ := initial_bound Q h hnn A u v huv hp hu hv .man
  obtain ⟨bw, dwu, dwv⟩ := initial_bound Q h hnn A u v huv hp hu hv .woman
  obtain ⟨b1, b2, dmu2, dwv2, -, -, dmx, dwx⟩ := assoc_bound Q h hnn hs
  obtain ⟨g1, g2⟩ := assoc_deg Q hs
  have cm := case1 hh dmu2 dmv dmx bm b1
  have cw := case1 hh dwv2 dwu dwx (pA := Q.pLoss h .woman A) (by linarith) b2
  rw [Aval_eq dmx] at cm
  rw [Aval_eq dwx] at cw
  have i1 := ite_iff g1 (h 1)
  have i2 := ite_iff g2 (h 1)
  have lsA := lam_star Q h A (by linarith [hpos hh dmu, hpos hh dmv])
    (by linarith [hpos hh dwu, hpos hh dwv])
  have q1 := hpos hh (show 1 ≤ Q.dL .man u - 1 by omega)
  have q2 := hpos hh (show 1 ≤ Q.dL .woman v - 1 by omega)
  have lsB := lam_star Q h B (by linarith [hpos hh dmu, hpos hh dmv, hpos hh dmx])
    (by linarith [hpos hh dwu, hpos hh dwv, hpos hh dwx])
  linarith

theorem final2 (h : ℕ → ℝ) (hh : IsAdmissible h) {A : Fin Q.R} (hA : Q.IsInitialSwap A)
    {u v : Fin n} (huv : u ≠ v) (hp : Q.participants A = {u, v}) (hu : Q.IsFirst u A)
    (hv : Q.IsFirst v A) (x1 : Fin n) (B1 : Fin Q.R) (hs1 : Assoc Q A x1 u v B1)
    (x2 : Fin n) (B2 : Fin Q.R) (hs2 : Assoc Q A x2 v u B2) :
    Q.DStar h A ≤ (h 2 / 2) * ((Q.NA .man A : ℝ) + (Q.NA .woman A : ℝ)) := by
  have hnn : ∀ r, 1 ≤ r → 0 ≤ h r := fun r hr => (hpos hh hr).le
  have hp' : Q.participants A = {v, u} := by rw [hp, Finset.pair_comm]
  have hx12 : x1 ≠ x2 := by
    intro he
    rw [he] at hs1
    exact huv (assoc_unique_y Q hs1 hs2)
  have hX : Q.XA A = {x1, x2} := by
    ext x'
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      obtain ⟨y, z, B', hs'⟩ := assoc_of_XA Q A x' hx
      rcases pair_cases huv hs'.2.2.2.1 (hp.symm.trans hs'.2.2.2.2.2.2.1) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at hs'; exact Or.inl (assoc_unique_x Q hs' hs1)
      · rw [h1, h2] at hs'; exact Or.inr (assoc_unique_x Q hs' hs2)
    · rintro (hx | hx)
      · rw [hx]; exact XA_of_assoc Q hs1
      · rw [hx]; exact XA_of_assoc Q hs2
  have hx1X : x1 ∈ Q.XA A := by rw [hX]; simp
  have hx2X : x2 ∈ Q.XA A := by rw [hX]; simp
  have bmu := beta_w Q h hA huv hp hu hv hu .man
  have bwu := beta_w Q h hA huv hp hu hv hu .woman
  have bmv := beta_w Q h hA huv hp hu hv hv .man
  have bwv := beta_w Q h hA huv hp hu hv hv .woman
  rw [if_pos (by rw [parent_man_iff Q huv hp hu]; exact ⟨x1, B1, hs1⟩)] at bmu
  rw [if_pos (by rw [parent_woman_iff Q huv hp hu]; exact ⟨x2, B2, hs2⟩)] at bwu
  rw [if_pos (by rw [parent_man_iff Q huv.symm hp' hv]; exact ⟨x2, B2, hs2⟩)] at bmv
  rw [if_pos (by rw [parent_woman_iff Q huv.symm hp' hv]; exact ⟨x1, B1, hs1⟩)] at bwv
  have bmx1 := beta_x Q h hx1X .man
  have bwx1 := beta_x Q h hx1X .woman
  have bmx2 := beta_x Q h hx2X .man
  have bwx2 := beta_x Q h hx2X .woman
  have hNm := hN Q h A .man
  have hNw := hN Q h A .woman
  rw [hX, Finset.sum_pair hx12] at hNm hNw
  rw [DStar_eq Q h huv hp hu hv, hX, Finset.sum_pair hx12, Finset.sum_pair hx12,
    atFirst_eq Q hs1.1, atFirst_eq Q hs2.1]
  obtain ⟨bm, dmu, dmv⟩ := initial_bound Q h hnn A u v huv hp hu hv .man
  obtain ⟨bw, dwu, dwv⟩ := initial_bound Q h hnn A u v huv hp hu hv .woman
  obtain ⟨b1m, b1w, dmu2, dwv2, -, -, dmx1, dwx1⟩ := assoc_bound Q h hnn hs1
  obtain ⟨b2m, b2w, dmv2, dwu2, -, -, dmx2, dwx2⟩ := assoc_bound Q h hnn hs2
  obtain ⟨g1, g2⟩ := assoc_deg Q hs1
  obtain ⟨g3, g4⟩ := assoc_deg Q hs2
  have cm := case2 hh dmu2 dmv2 dmx1 dmx2 bm b1m b2m
  have cw := case2 hh dwv2 dwu2 dwx1 dwx2 (pA := Q.pLoss h .woman A) (by linarith) b1w b2w
  rw [Aval_eq dmx1, Aval_eq dmx2] at cm
  rw [Aval_eq dwx1, Aval_eq dwx2] at cw
  have i1 := ite_iff g1 (h 1)
  have i2 := ite_iff g2 (h 1)
  have i3 := ite_iff g3 (h 1)
  have i4 := ite_iff g4 (h 1)
  have lsA := lam_star Q h A (by linarith [hpos hh dmu, hpos hh dmv])
    (by linarith [hpos hh dwu, hpos hh dwv])
  have q1 := hpos hh (show 1 ≤ Q.dL .man u - 1 by omega)
  have q2 := hpos hh (show 1 ≤ Q.dL .woman v - 1 by omega)
  have q3 := hpos hh (show 1 ≤ Q.dL .man v - 1 by omega)
  have q4 := hpos hh (show 1 ≤ Q.dL .woman u - 1 by omega)
  have lsB1 := lam_star Q h B1 (by linarith [hpos hh dmu, hpos hh dmv, hpos hh dmx1])
    (by linarith [hpos hh dwu, hpos hh dwv, hpos hh dwx1])
  have lsB2 := lam_star Q h B2 (by linarith [hpos hh dmu, hpos hh dmv, hpos hh dmx2])
    (by linarith [hpos hh dwu, hpos hh dwv, hpos hh dwx2])
  linarith

end final

end Dev.L62

theorem chk_lemma_6_2 {n : ℕ} (h : ℕ → ℝ) (hh : IsAdmissible h) (Q : Member n) (A : Fin Q.R)
    (hA : Q.IsInitialSwap A) :
    Q.DStar h A ≤ (h 2 / 2) * ((Q.NA .man A : ℝ) + (Q.NA .woman A : ℝ)) := by
  obtain ⟨u, v, huv, hp⟩ := Finset.card_eq_two.mp hA.1
  have hu : Q.IsFirst u A := hA.2 u (by rw [hp]; simp)
  have hv : Q.IsFirst v A := hA.2 v (by rw [hp]; simp)
  have hp' : Q.participants A = {v, u} := by rw [hp, Finset.pair_comm]
  by_cases hU : ∃ x B, Dev.L62.Assoc Q A x u v B
  · by_cases hV : ∃ x B, Dev.L62.Assoc Q A x v u B
    · obtain ⟨x1, B1, hs1⟩ := hU
      obtain ⟨x2, B2, hs2⟩ := hV
      exact Dev.L62.final2 Q h hh hA huv hp hu hv x1 B1 hs1 x2 B2 hs2
    · obtain ⟨x, B, hs⟩ := hU
      exact Dev.L62.final1 Q h hh hA huv hp hu hv x B hs hV
  · by_cases hV : ∃ x B, Dev.L62.Assoc Q A x v u B
    · obtain ⟨x, B, hs⟩ := hV
      exact Dev.L62.final1 Q h hh hA huv.symm hp' hv hu x B hs hU
    · exact Dev.L62.final0 Q h hh hA huv hp hu hv hU hV

end StableCount
end

theorem solution : type_of% @StableCount.chk_lemma_6_2 := @StableCount.chk_lemma_6_2
