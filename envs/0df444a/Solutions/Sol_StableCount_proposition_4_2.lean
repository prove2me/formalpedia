-- Prove2me | solution 1 for StableCount.proposition_4_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T00:09:57.625372+00:00
-- url     : https://prove2.me/submissions/d0f86d87-9440-4ddf-bed4-8a7a52078713

import Mathlib
import Definitions.Def_StableCount_Groups
import Theorems.Thm_StableCount_proposition_5_8
import Theorems.Thm_StableCount_lemma_5_2

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

end assoc

section loss

variable (Q : Member n)

theorem W_sub_one (h : ℕ → ℝ) {d : ℕ} (hd : 1 ≤ d) : W h d - W h (d - 1) = h d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  simp only [W, Nat.add_sub_cancel]
  rw [Finset.sum_Icc_succ_top (by omega)]
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

theorem card_le_dL (s : Sex) (i : Fin Q.R) (v : Fin n) :
    (Q.down i ∩ Q.chainOf s (Q.person s v)).card ≤ Q.dL s v :=
  Finset.card_le_card Finset.inter_subset_right

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

section adm

variable {h : ℕ → ℝ}

end adm


/-! ### Assembly -/

section final

variable {n : ℕ} (Q : Member n)

theorem atFirst_eq {x : Fin n} {B : Fin Q.R} (hx : Q.IsFirst x B) (f : Fin Q.R → ℝ) :
    Q.atFirst f x = f B := by
  obtain ⟨hv, rfl⟩ := hx
  simp [Member.atFirst, hv]

theorem lam_star (h : ℕ → ℝ) (i : Fin Q.R) (hm : 0 < Q.pLoss h .man i)
    (hw : 0 < Q.pLoss h .woman i) :
    2 * lam (Q.pStar h i) ≤ lam (Q.pLoss h .man i) + lam (Q.pLoss h .woman i) := by
  unfold Member.pStar
  exact lam_mid hm hw

end final

end Dev.L62

end StableCount
end

section
namespace StableCount

open StableMatching

namespace Dev.P42

open Dev.L52 Dev.L62

variable {n : ℕ}

section

variable (Q : Member n)

theorem mem_fg (v : Fin n) (i : Fin Q.R) : v ∈ Q.firstGroup i ↔ Q.IsFirst v i := by
  simp [Member.firstGroup]

theorem fg_sub_part (i : Fin Q.R) : Q.firstGroup i ⊆ Q.participants i := by
  intro v hv
  rw [mem_fg] at hv
  rw [mem_participants]
  exact ((isFirst_iff Q v i).mp hv).1

theorem fg_initial {A : Fin Q.R} (hA : Q.IsInitialSwap A) : Q.firstGroup A = Q.participants A := by
  refine Finset.Subset.antisymm (fg_sub_part Q A) fun v hv => ?_
  rw [mem_fg]; exact hA.2 v hv

theorem initial_not_exc {A : Fin Q.R} (hA : Q.IsInitialSwap A) : ¬ Q.IsExceptionalSwap A := by
  intro hE
  have := hE.1
  rw [fg_initial Q hA, hA.1] at this
  exact absurd this (by norm_num)

theorem V_of_first {v : Fin n} {i : Fin Q.R} (h : Q.IsFirst v i) : v ∈ Q.V := h.1

theorem XA_info {A : Fin Q.R} {x : Fin n} (hx : x ∈ Q.XA A) :
    ∃ B, Q.IsFirst x B ∧ Q.IsExceptionalSwap B ∧ Q.down B = {A, B} ∧ A ≠ B := by
  obtain ⟨y, z, B, hs⟩ := assoc_of_XA Q A x hx
  exact ⟨B, hs.1, hs.2.1, hs.2.2.2.2.2.2.2.2.2.1, hs.2.2.1.ne⟩

theorem XA_unique {A A' : Fin Q.R} {x : Fin n} (hx : x ∈ Q.XA A) (hx' : x ∈ Q.XA A') : A = A' := by
  obtain ⟨B, h1, -, h3, h4⟩ := XA_info Q hx
  obtain ⟨B', h1', -, h3', h4'⟩ := XA_info Q hx'
  have := isFirst_unique Q h1 h1'
  subst this
  have hA : A ∈ Q.down B := by rw [h3]; simp
  rw [h3'] at hA
  simp only [Finset.mem_insert, Finset.mem_singleton] at hA
  rcases hA with h | h
  · exact h
  · exact absurd h h4

/-- every element of `K_A` has as first rotation `A` itself or an exceptional swap -/
theorem KA_info {A : Fin Q.R} {v : Fin n} (hv : v ∈ Q.KA A) :
    Q.IsFirst v A ∨ ∃ B, Q.IsFirst v B ∧ Q.IsExceptionalSwap B := by
  unfold Member.KA at hv
  rcases Finset.mem_union.mp hv with h | h
  · exact Or.inl ((mem_fg Q v A).mp h)
  · obtain ⟨B, h1, h2, -⟩ := XA_info Q h
    exact Or.inr ⟨B, h1, h2⟩

theorem mem_P (A : Fin Q.R) : A ∈ Q.initialSwaps ↔ Q.IsInitialSwap A := by
  simp [Member.initialSwaps]

theorem mem_O (i : Fin Q.R) : i ∈ Q.ordinary ↔ Q.IsOrdinary i := by
  simp [Member.ordinary]

theorem V_eq : Q.V = Q.initialSwaps.biUnion Q.KA ∪ Q.ordinary.biUnion Q.firstGroup := by
  ext v
  simp only [Finset.mem_union, Finset.mem_biUnion]
  constructor
  · intro hv
    have hF : Q.IsFirst v (Q.first v hv) := ⟨hv, rfl⟩
    set b := Q.first v hv
    by_cases hI : Q.IsInitialSwap b
    · left
      refine ⟨b, (mem_P Q b).mpr hI, ?_⟩
      unfold Member.KA
      exact Finset.mem_union_left _ ((mem_fg Q v b).mpr hF)
    by_cases hE : Q.IsExceptionalSwap b
    · left
      obtain ⟨A, y, z, hs⟩ := assoc_of_exc Q v b hF hE
      refine ⟨A, (mem_P Q A).mpr ?_, ?_⟩
      · obtain ⟨-, -, -, hyz, -, -, hp, hy, hz, -⟩ := hs
        refine ⟨by rw [hp, Finset.card_pair hyz], fun w hw => ?_⟩
        rw [hp] at hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hy
        · exact hz
      · unfold Member.KA
        exact Finset.mem_union_right _ (XA_of_assoc Q hs)
    · right
      refine ⟨b, (mem_O Q b).mpr ⟨⟨v, (mem_fg Q v b).mpr hF⟩, hI, hE⟩, (mem_fg Q v b).mpr hF⟩
  · rintro (⟨A, -, hA⟩ | ⟨i, -, hi⟩)
    · rcases KA_info Q hA with h | ⟨B, h, -⟩
      · exact V_of_first Q h
      · exact V_of_first Q h
    · exact V_of_first Q ((mem_fg Q v i).mp hi)

theorem disj_P : (↑Q.initialSwaps : Set (Fin Q.R)).PairwiseDisjoint Q.KA := by
  intro A hA A' hA' hne
  rw [Finset.mem_coe, mem_P] at hA hA'
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro v hv hv'
  unfold Member.KA at hv hv'
  rcases Finset.mem_union.mp hv with h | h <;> rcases Finset.mem_union.mp hv' with h' | h'
  · exact hne (isFirst_unique Q ((mem_fg Q v A).mp h) ((mem_fg Q v A').mp h'))
  · obtain ⟨B, h1, h2, -⟩ := XA_info Q h'
    have := isFirst_unique Q ((mem_fg Q v A).mp h) h1
    subst this
    exact initial_not_exc Q hA h2
  · obtain ⟨B, h1, h2, -⟩ := XA_info Q h
    have := isFirst_unique Q ((mem_fg Q v A').mp h') h1
    subst this
    exact initial_not_exc Q hA' h2
  · exact hne (XA_unique Q h h')

theorem disj_O : (↑Q.ordinary : Set (Fin Q.R)).PairwiseDisjoint Q.firstGroup := by
  intro A _ A' _ hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro v hv hv'
  exact hne (isFirst_unique Q ((mem_fg Q v A).mp hv) ((mem_fg Q v A').mp hv'))

theorem disj_PO : Disjoint (Q.initialSwaps.biUnion Q.KA) (Q.ordinary.biUnion Q.firstGroup) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  simp only [Finset.mem_biUnion] at hv hv'
  obtain ⟨A, hA, hvA⟩ := hv
  obtain ⟨i, hi, hvi⟩ := hv'
  rw [mem_P] at hA
  rw [mem_O] at hi
  have hFi := (mem_fg Q v i).mp hvi
  rcases KA_info Q hvA with h | ⟨B, h, hB⟩
  · have := isFirst_unique Q h hFi
    subst this
    exact hi.2.1 hA
  · have := isFirst_unique Q h hFi
    subst this
    exact hi.2.2 hB

theorem sum_partition (f : Fin n → ℝ) :
    ∑ v ∈ Q.V, f v = ∑ A ∈ Q.initialSwaps, ∑ v ∈ Q.KA A, f v +
      ∑ i ∈ Q.ordinary, ∑ v ∈ Q.firstGroup i, f v := by
  rw [V_eq Q, Finset.sum_union (disj_PO Q), Finset.sum_biUnion (disj_P Q),
    Finset.sum_biUnion (disj_O Q)]

theorem sum_fg (f : Fin Q.R → ℝ) (i : Fin Q.R) :
    ∑ v ∈ Q.firstGroup i, Q.atFirst f v = ((Q.firstGroup i).card : ℝ) * f i := by
  rw [Finset.sum_congr rfl fun v hv => atFirst_eq Q ((mem_fg Q v i).mp hv) f]
  simp

theorem pLoss_pos (h : ℕ → ℝ) (hh : IsAdmissible h) (s : Sex) (i : Fin Q.R) :
    0 < Q.pLoss h s i := by
  have hnn : ∀ r, 1 ≤ r → 0 ≤ h r := fun r hr => (hh.1 r hr).le
  obtain ⟨v, hv⟩ : ∃ v, Q.moves s i (Q.person s v) := by
    obtain ⟨m, hm⟩ := exists_move Q i
    cases s
    · exact ⟨m, hm⟩
    · refine ⟨(Q.μ 0).symm (Q.μ i.castSucc m), ?_⟩
      show Q.moves .woman i (Q.μ 0 ((Q.μ 0).symm (Q.μ i.castSucc m)))
      rw [Equiv.apply_symm_apply]
      exact (moves_woman_iff Q i m).mpr hm
  rw [pLoss_eq]
  refine Finset.sum_pos' (fun p _ => tm_nonneg Q h hnn s i p) ⟨v, Finset.mem_univ _, ?_⟩
  have hc1 : 1 ≤ (Q.down i ∩ Q.chainOf s (Q.person s v)).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_inter.mpr
      ⟨(mem_down' Q i i).mpr (le_rfl' Q i), (mem_chainOf Q s _ i).mpr hv⟩⟩
  have hcd := card_le_dL Q s i v
  unfold tm
  generalize (Q.down i ∩ Q.chainOf s (Q.person s v)).card = c at hc1 hcd ⊢
  generalize Q.dL s v = d at hcd ⊢
  have e1 := W_sub_one h (le_trans hc1 hcd)
  have e2 := W_sub_nonneg h hnn (d - 1) (c - 1)
  rw [show d - 1 - (c - 1) = d - c by omega] at e2
  have := hh.1 d (by omega)
  linarith

theorem ordinary_bound (h : ℕ → ℝ) (hh : IsAdmissible h) (i : Fin Q.R) :
    ∑ v ∈ Q.firstGroup i, (Q.atFirst (fun j => lam (Q.pStar h j)) v -
        (1 / 2) * (Q.beta h .man v + Q.beta h .woman v)) ≤
      -((1 / 2) * (Q.Delta h .man i + Q.Delta h .woman i)) := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_fg, Finset.sum_add_distrib]
  unfold Member.Delta
  have hl := lam_star Q h i (pLoss_pos Q h hh .man i) (pLoss_pos Q h hh .woman i)
  have hc : (0 : ℝ) ≤ ((Q.firstGroup i).card : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hl hc]

theorem initial_eq (h : ℕ → ℝ) {A : Fin Q.R} (hA : Q.IsInitialSwap A) :
    ∑ v ∈ Q.KA A, (Q.atFirst (fun j => lam (Q.pStar h j)) v -
        (1 / 2) * (Q.beta h .man v + Q.beta h .woman v)) = Q.DStar h A := by
  have hdisj : Disjoint (Q.firstGroup A) (Q.XA A) := by
    rw [Finset.disjoint_left]
    intro w hw hwX
    obtain ⟨B, h1, -, -, h4⟩ := XA_info Q hwX
    exact h4 (isFirst_unique Q ((mem_fg Q w A).mp hw) h1)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold Member.DStar
  have hKA : Q.KA A = Q.firstGroup A ∪ Q.XA A := rfl
  rw [hKA, Finset.sum_union hdisj, sum_fg, fg_initial Q hA, hA.1]
  push_cast
  ring

end

end Dev.P42

open Dev.P42 in
theorem chk_proposition_4_2 {n : ℕ} (h : ℕ → ℝ) (hh : IsAdmissible h) (Q : Member n) (hQ : Q.R ≠ 0) :
    ∑ v ∈ Q.V, Q.atFirst (fun i => lam (Q.pStar h i)) v ≤ ∑ v ∈ Q.V, Q.atFirst (Q.qStar h) v := by
  -- Step 1: the right-hand side
  have hq : ∀ v, Q.atFirst (Q.qStar h) v =
      (Q.atFirst (Q.qLoss h .man) v + Q.atFirst (Q.qLoss h .woman) v) / 2 := by
    intro v
    unfold Member.atFirst
    split_ifs <;> simp [Member.qStar]
  have hR : ∑ v ∈ Q.V, Q.atFirst (Q.qStar h) v =
      (Q.U h .man + Q.U h .woman) / 2 +
        (1 / 2) * ∑ v ∈ Q.V, (Q.beta h .man v + Q.beta h .woman v) := by
    rw [Finset.sum_congr rfl fun v _ => hq v, ← Finset.sum_div, Finset.sum_add_distrib,
      (lemma_5_2 h Q .man).1, (lemma_5_2 h Q .woman).1, Finset.sum_add_distrib]
    unfold Member.U
    ring
  -- Step 2: the partition
  set g : Fin n → ℝ := fun v => Q.atFirst (fun j => lam (Q.pStar h j)) v -
    (1 / 2) * (Q.beta h .man v + Q.beta h .woman v) with hg
  have hP := sum_partition Q g
  have h1 : ∑ A ∈ Q.initialSwaps, ∑ v ∈ Q.KA A, g v = ∑ A ∈ Q.initialSwaps, Q.DStar h A :=
    Finset.sum_congr rfl fun A hA => initial_eq Q h ((mem_P Q A).mp hA)
  have h2 : ∑ i ∈ Q.ordinary, ∑ v ∈ Q.firstGroup i, g v ≤
      ∑ i ∈ Q.ordinary, -((1 / 2) * (Q.Delta h .man i + Q.Delta h .woman i)) :=
    Finset.sum_le_sum fun i _ => ordinary_bound Q h hh i
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at h2
  have h58 := proposition_5_8 h hh Q
  have hgsum : ∑ v ∈ Q.V, g v = ∑ v ∈ Q.V, Q.atFirst (fun i => lam (Q.pStar h i)) v -
      (1 / 2) * ∑ v ∈ Q.V, (Q.beta h .man v + Q.beta h .woman v) := by
    rw [hg, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hR]
  linarith

end StableCount
end

theorem solution : type_of% @StableCount.chk_proposition_4_2 := @StableCount.chk_proposition_4_2
