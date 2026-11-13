-- Prove2me | solution 1 for StableCount.proposition_5_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T00:22:07.147196+00:00
-- url     : https://prove2.me/submissions/35c156dd-a889-487f-bf17-3497a02f3427

import Mathlib
import Definitions.Def_StableCount_Groups
import Theorems.Thm_StableCount_lemma_6_2
import Theorems.Thm_StableCount_lemma_8_3

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

open Classical in
theorem rank_sum {R : ℕ} (g : ℕ → ℝ) (S : Finset (Fin R)) :
    ∑ i ∈ S, g ((S.filter fun j => j ≤ i).card) = ∑ r ∈ Finset.Icc 1 S.card, g r := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S ha ih =>
    have han : a ∉ S := fun h => lt_irrefl _ (ha a h)
    rw [Finset.sum_insert han, Finset.card_insert_of_notMem han]
    have h1 : ((insert a S).filter fun j => j ≤ a).card = S.card + 1 := by
      have : (insert a S).filter (fun j => j ≤ a) = insert a S := by
        apply Finset.filter_true_of_mem
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact le_refl _
        · exact (ha j hj).le
      rw [this, Finset.card_insert_of_notMem han]
    have h2 : ∀ i ∈ S, ((insert a S).filter fun j => j ≤ i).card = (S.filter fun j => j ≤ i).card := by
      intro i hi
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hj | hj, hji⟩
        · exact absurd (hj ▸ hji) (not_le.mpr (ha i hi))
        · exact ⟨hj, hji⟩
      · rintro ⟨hj, hji⟩
        exact ⟨Or.inr hj, hji⟩
    rw [h1, Finset.sum_congr rfl (fun i hi => by rw [h2 i hi]), ih,
      Finset.sum_Icc_succ_top (by omega)]
    ring

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

theorem first_rank (Q : Member n) (s : Sex) (v : Fin n) (hv : v ∈ Q.V) :
    Q.rank s (Q.person s v) (Q.first v hv) = 1 := by
  obtain ⟨h1, h2⟩ := first_spec Q v hv
  unfold Member.rank
  rw [Finset.card_eq_one]
  refine ⟨Q.first v hv, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hj, hji⟩
    rcases hji.lt_or_eq with hlt | heq
    · exfalso
      rw [mem_chainOf] at hj
      cases s
      · exact h2 j hlt hj
      · have e0 := man_eq_first Q v hv
        change (Q.μ j.castSucc).symm (Q.μ 0 v) ≠ (Q.μ j.succ).symm (Q.μ 0 v) at hj
        apply hj
        have hjl : (j : ℕ) < Q.first v hv := hlt
        have a1 : (Q.μ j.castSucc).symm (Q.μ 0 v) = v := by
          rw [Equiv.symm_apply_eq]; exact (e0 _ (by simp; omega)).symm
        have a2 : (Q.μ j.succ).symm (Q.μ 0 v) = v := by
          rw [Equiv.symm_apply_eq]; exact (e0 _ (by simp; omega)).symm
        rw [a1, a2]
    · exact heq
  · intro hj
    exact ⟨hj ▸ first_mem_chain Q s v hv, hj ▸ le_refl _⟩

theorem chain_empty_of_not_V (Q : Member n) (s : Sex) (v : Fin n) (hv : v ∉ Q.V) :
    Q.chainOf s (Q.person s v) = ∅ := by
  have hman : ∀ i : Fin Q.R, ¬ Q.moves .man i v := by
    intro i hi
    apply hv
    unfold Member.V
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold Member.dL Member.deg
    exact Finset.card_pos.mpr ⟨i, (mem_chainOf Q .man v i).mpr hi⟩
  ext i
  rw [mem_chainOf]
  simp only [Finset.notMem_empty, iff_false]
  cases s
  · exact hman i
  · have e0 : ∀ m : Fin (Q.R + 1), Q.μ m v = Q.μ 0 v := by
      intro m
      have := partner_eq_zero Q .man v m (fun k _ => hman k)
      simpa [partner] using this
    change ¬ ((Q.μ i.castSucc).symm (Q.μ 0 v) ≠ (Q.μ i.succ).symm (Q.μ 0 v))
    have a1 : (Q.μ i.castSucc).symm (Q.μ 0 v) = v := by
      rw [Equiv.symm_apply_eq]; exact (e0 _).symm
    have a2 : (Q.μ i.succ).symm (Q.μ 0 v) = v := by
      rw [Equiv.symm_apply_eq]; exact (e0 _).symm
    rw [a1, a2]; exact fun h => h rfl

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

theorem tm_one (h : ℕ → ℝ) (s : Sex) (i : Fin Q.R) (v : Fin n)
    (hc : (Q.down i ∩ Q.chainOf s (Q.person s v)).card = 1) :
    tm Q h s i v = h (Q.dL s v) ∧ 1 ≤ Q.dL s v := by
  have hd := card_le_dL Q s i v
  rw [hc] at hd
  refine ⟨?_, hd⟩
  unfold tm
  rw [hc]
  exact W_sub_one h hd

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

end adm


/-! ### Assembly -/

section final

variable {n : ℕ} (Q : Member n)

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

theorem atFirst_eq {x : Fin n} {B : Fin Q.R} (hx : Q.IsFirst x B) (f : Fin Q.R → ℝ) :
    Q.atFirst f x = f B := by
  obtain ⟨hv, rfl⟩ := hx
  simp [Member.atFirst, hv]

end final

end Dev.L62

end StableCount
end

section
namespace StableCount
open StableMatching
namespace Dev.L83
open Dev.L52 Dev.L62

theorem exp_pow' (b : ℝ) (k : ℕ) : Real.exp (-((k : ℝ) * b)) = Real.exp (-b) ^ k := by
  rw [← Real.exp_nat_mul]; congr 1; ring

/-- `λ(t) ≤ λ(2t) + ln 2` -/
theorem lam_le_lam_two {t : ℝ} (ht : 0 < t) : lam t ≤ lam (2 * t) + Real.log 2 := by
  unfold lam
  have h1 := ose_pos ht
  have h2 := ose_pos (by linarith : 0 < 2 * t)
  have e : Real.exp (-(2 * t)) = Real.exp (-t) ^ 2 := by
    have := exp_pow' t 2; push_cast at this; exact this
  have key : 1 - Real.exp (-(2 * t)) ≤ 2 * (1 - Real.exp (-t)) := by
    rw [e]; have := Real.exp_pos (-t); nlinarith
  have := Real.log_le_log h2 key
  rw [Real.log_mul (by norm_num) h1.ne'] at this
  linarith

section adm
variable {h : ℕ → ℝ}

end adm

section cover
variable {h : ℕ → ℝ}

end cover

section final
variable {n : ℕ} (Q : Member n)

end final

section delta
variable {h : ℕ → ℝ}

/-- Lemma 5.7 for a singleton group: `λ(p) ≤ β` when `p ≥ h_d`. -/
theorem delta_nonneg (hh : IsAdmissible h) {d : ℕ} (hd : 1 ≤ d) {p : ℝ} (hp : h d ≤ p) :
    lam p ≤ Hsum h d + 2 * h 1 + (if 2 ≤ d then h 2 else 0) := by
  have pd := hpos hh hd
  have a := lam_anti' pd hp
  have b := lam_le_lam_two pd
  have c := L56 hh hd
  have H1 : Real.log 2 ≤ 2 * h 1 := hh.2.2.1
  linarith

end delta

end Dev.L83
end StableCount
end

section
set_option autoImplicit false

namespace StableCount
open StableMatching
namespace Dev.L83
open Dev.L52 Dev.L62

variable {n : ℕ}

/-- the other sex -/
def opp : Sex → Sex
  | .man => .woman
  | .woman => .man

/-- partner labels: `pm Q s t ℓ` is the label of the partner, at time `t`, of the person of sex `s`
with label `ℓ` -/
def pm (Q : Member n) : Sex → Fin (Q.R + 1) → Equiv.Perm (Fin n)
  | .man, t => (Q.μ t).trans (Q.μ 0).symm
  | .woman, t => ((Q.μ t).trans (Q.μ 0).symm).symm

/-- the person of sex `s` with label `ℓ` moves at step `k` -/
def mv (Q : Member n) (s : Sex) (k : Fin Q.R) (ℓ : Fin n) : Prop := Q.moves s k (Q.person s ℓ)

instance (Q : Member n) (s : Sex) (k : Fin Q.R) (ℓ : Fin n) : Decidable (mv Q s k ℓ) := by
  unfold mv; infer_instance

section basic
variable (Q : Member n)

theorem pm_opp (s : Sex) (t : Fin (Q.R + 1)) : pm Q (opp s) t = (pm Q s t).symm := by
  cases s <;> rfl

theorem pm_zero (s : Sex) (ℓ : Fin n) : pm Q s 0 ℓ = ℓ := by
  cases s <;> simp [pm]

theorem mv_iff (s : Sex) (k : Fin Q.R) (ℓ : Fin n) :
    mv Q s k ℓ ↔ pm Q s k.castSucc ℓ ≠ pm Q s k.succ ℓ := by
  cases s
  · simp [mv, Member.moves, Member.person, pm]
  · simp [mv, Member.moves, Member.person, pm]

theorem pm_const (s : Sex) (ℓ : Fin n) (a b : Fin (Q.R + 1)) (hab : a ≤ b)
    (h : ∀ k : Fin Q.R, (a : ℕ) ≤ k → (k : ℕ) < b → ¬ mv Q s k ℓ) : pm Q s b ℓ = pm Q s a ℓ := by
  cases s
  · have := partner_eq_of_no_move Q .man ℓ a b hab h
    simp only [partner] at this
    simp [pm, this]
  · have := partner_eq_of_no_move Q .woman (Q.μ 0 ℓ) a b hab h
    simp only [partner] at this
    simp [pm, this]

/-- a change of partner needs a step in between -/
theorem exists_step (s : Sex) (ℓ : Fin n) (a b : Fin (Q.R + 1)) (hab : a ≤ b)
    (h : pm Q s b ℓ ≠ pm Q s a ℓ) : ∃ k : Fin Q.R, (a : ℕ) ≤ k ∧ (k : ℕ) < b ∧ mv Q s k ℓ := by
  by_contra hc
  push Not at hc
  exact h (pm_const Q s ℓ a b hab fun k h1 h2 hm => hc k h1 h2 hm)

theorem norep_man (k : Fin Q.R) (ℓ : Fin n) (hk : mv Q .man k ℓ) (i j : Fin (Q.R + 1))
    (hi : i ≤ k.castSucc) (hj : k.succ ≤ j) : pm Q .man j ℓ ≠ pm Q .man i ℓ := by
  have := no_return Q ℓ k hk i j hi hj
  simpa [pm] using this

/-- the opposite person moves iff their current holder moves -/
theorem opp_mv (s : Sex) (k : Fin Q.R) (ℓ : Fin n) :
    mv Q (opp s) k ℓ ↔ mv Q s k ((pm Q s k.castSucc).symm ℓ) := by
  rw [mv_iff, mv_iff, pm_opp, pm_opp]
  constructor
  · intro h1 h2
    apply h1
    rw [Equiv.apply_symm_apply] at h2
    exact ((Equiv.symm_apply_eq _).mpr h2).symm
  · intro h1 h2
    apply h1
    rw [Equiv.apply_symm_apply, h2, Equiv.apply_symm_apply]

theorem norep_of (s : Sex)
    (H : ∀ (k : Fin Q.R) (ℓ : Fin n), mv Q s k ℓ → ∀ i j : Fin (Q.R + 1), i ≤ k.castSucc →
      k.succ ≤ j → pm Q s j ℓ ≠ pm Q s i ℓ)
    (k : Fin Q.R) (ℓ : Fin n) (hk : mv Q (opp s) k ℓ) (i j : Fin (Q.R + 1))
    (hi : i ≤ k.castSucc) (hj : k.succ ≤ j) : pm Q (opp s) j ℓ ≠ pm Q (opp s) i ℓ := by
  intro heq
  simp only [pm_opp] at heq
  set m := (pm Q s i).symm ℓ with hm
  have hij : i ≤ j := le_trans hi (le_trans (Fin.castSucc_le_succ k) hj)
  have h1 : pm Q s i m = ℓ := by simp [hm]
  have h2 : pm Q s j m = ℓ := by rw [← heq]; simp
  by_cases hst : ∃ k' : Fin Q.R, (i : ℕ) ≤ k' ∧ (k' : ℕ) < j ∧ mv Q s k' m
  · obtain ⟨k', a1, a2, a3⟩ := hst
    exact H k' m a3 i j (Fin.le_def.mpr (by simpa using a1)) (Fin.le_def.mpr (by simpa using a2))
      (h2.trans h1.symm)
  · push Not at hst
    have hc : pm Q s k.castSucc m = ℓ := by
      rw [pm_const Q s m i k.castSucc hi (fun k' a1 a2 => hst k' a1 (by
        have : (k.castSucc : ℕ) ≤ j := le_trans (by simp) (Fin.le_def.mp hj)
        omega)), h1]
    have hk' := (opp_mv Q s k ℓ).mp hk
    rw [show (pm Q s k.castSucc).symm ℓ = m by rw [← hc]; simp] at hk'
    exact hst k (Fin.le_def.mp hi) (by have := Fin.le_def.mp hj; simp at this; omega) hk'

theorem norep (s : Sex) (k : Fin Q.R) (ℓ : Fin n) (hk : mv Q s k ℓ) (i j : Fin (Q.R + 1))
    (hi : i ≤ k.castSucc) (hj : k.succ ≤ j) : pm Q s j ℓ ≠ pm Q s i ℓ := by
  cases s
  · exact norep_man Q k ℓ hk i j hi hj
  · exact norep_of Q .man (norep_man Q) k ℓ hk i j hi hj

theorem chain_le (s : Sex) {i j : Fin Q.R} {ℓ : Fin n} (hi : mv Q s i ℓ) (hj : mv Q s j ℓ)
    (hij : i < j) : Q.le i j :=
  le_of_chain Q s (Q.person s ℓ) i j hij hi hj

end basic

section first
variable (Q : Member n)

theorem mem_V_of_mv (s : Sex) {k : Fin Q.R} {ℓ : Fin n} (h : mv Q s k ℓ) : ℓ ∈ Q.V := by
  by_contra hv
  have := chain_empty_of_not_V Q s ℓ hv
  have hk : k ∈ Q.chainOf s (Q.person s ℓ) := (mem_chainOf Q s _ k).mpr h
  rw [this] at hk
  simp at hk

theorem isFirst_mv (s : Sex) {ℓ : Fin n} {i : Fin Q.R} (h : Q.IsFirst ℓ i) :
    mv Q s i ℓ ∧ ∀ k, k < i → ¬ mv Q s k ℓ := by
  obtain ⟨hv, rfl⟩ := h
  have h1 := first_mem_chain Q s ℓ hv
  have h2 := first_rank Q s ℓ hv
  refine ⟨(mem_chainOf Q s _ _).mp h1, fun k hk hm => ?_⟩
  have hk' : k ∈ Q.chainOf s (Q.person s ℓ) := (mem_chainOf Q s _ k).mpr hm
  unfold Member.rank at h2
  have hsub : ({k, Q.first ℓ hv} : Finset (Fin Q.R)) ⊆
      (Q.chainOf s (Q.person s ℓ)).filter fun j => j ≤ Q.first ℓ hv := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hk', hk.le⟩
    · exact Finset.mem_filter.mpr ⟨h1, le_refl _⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hk.ne, h2] at this
  omega

theorem isFirst_of_mv (s : Sex) {ℓ : Fin n} {i : Fin Q.R} (h : mv Q s i ℓ)
    (hno : ∀ k, k < i → ¬ mv Q s k ℓ) : Q.IsFirst ℓ i := by
  have hv := mem_V_of_mv Q s h
  have hf : Q.IsFirst ℓ (Q.first ℓ hv) := ⟨hv, rfl⟩
  obtain ⟨m1, m2⟩ := isFirst_mv Q s hf
  rcases lt_trichotomy (Q.first ℓ hv) i with hl | he | hl
  · exact absurd m1 (hno _ hl)
  · rw [← he]; exact hf
  · exact absurd h (m2 _ hl)

theorem exists_first (s : Sex) {j : Fin Q.R} {ℓ : Fin n} (h : mv Q s j ℓ) :
    ∃ f, Q.IsFirst ℓ f ∧ f ≤ j := by
  classical
  have hne : (Finset.univ.filter fun k => mv Q s k ℓ).Nonempty := ⟨j, by simp [h]⟩
  set f := (Finset.univ.filter fun k => mv Q s k ℓ).min' hne
  have hf : f ∈ Finset.univ.filter fun k => mv Q s k ℓ := Finset.min'_mem _ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
  refine ⟨f, isFirst_of_mv Q s hf fun k hk hm => ?_, Finset.min'_le _ _ (by simp [h])⟩
  exact absurd (Finset.min'_le _ k (by simp [hm])) (not_le.mpr hk)

theorem support_iff (s : Sex) (k : Fin Q.R) (ℓ : Fin n) :
    ℓ ∈ Q.support k ↔ ∃ j, Q.le j k ∧ mv Q s j ℓ := by
  simp only [Member.support, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, hjk⟩
    exact ⟨j, hjk, (isFirst_mv Q s hj).1⟩
  · rintro ⟨j, hjk, hm⟩
    obtain ⟨f, hf, hfj⟩ := exists_first Q s hm
    refine ⟨f, hf, ?_⟩
    rcases hfj.lt_or_eq with hl | he
    · exact le_tr Q (chain_le Q s (isFirst_mv Q s hf).1 hm hl) hjk
    · rw [he]; exact hjk

theorem support_mono {a b : Fin Q.R} (h : Q.le a b) : Q.support a ⊆ Q.support b := by
  intro ℓ hℓ
  rw [support_iff Q .man] at hℓ ⊢
  obtain ⟨j, hj, hm⟩ := hℓ
  exact ⟨j, le_tr Q hj h, hm⟩

theorem mem_support_self (s : Sex) {k : Fin Q.R} {ℓ : Fin n} (h : mv Q s k ℓ) :
    ℓ ∈ Q.support k :=
  (support_iff Q s k ℓ).mpr ⟨k, le_rfl' Q k, h⟩

/-- steps of one person below `k` in the order are exactly those with smaller index -/
theorem chain_le_iff (s : Sex) {j k : Fin Q.R} {ℓ : Fin n} (hj : mv Q s j ℓ) (hk : mv Q s k ℓ) :
    Q.le j k ↔ j ≤ k := by
  constructor
  · exact le_idx Q
  · intro h
    rcases h.lt_or_eq with hl | he
    · exact chain_le Q s hj hk hl
    · rw [he]; exact le_rfl' Q k

end first

section downperm
variable (Q : Member n)

/-- a downset of `Q.le` -/
def IsDn (D : Finset (Fin Q.R)) : Prop := ∀ a ∈ D, ∀ b, Q.le b a → b ∈ D

theorem isDn_down (k : Fin Q.R) : IsDn Q (Q.down k) := by
  intro a ha b hb
  rw [mem_down'] at ha ⊢
  exact le_tr Q hb ha

/-- `t` is the time just after the last step of `ℓ` in `D` -/
def IsTD (s : Sex) (D : Finset (Fin Q.R)) (ℓ : Fin n) (t : Fin (Q.R + 1)) : Prop :=
  ∀ j, mv Q s j ℓ → (j ∈ D ↔ (j : ℕ) < t)

theorem exists_tD (s : Sex) {D : Finset (Fin Q.R)} (hD : IsDn Q D) (ℓ : Fin n) :
    ∃ t, IsTD Q s D ℓ t := by
  classical
  by_cases hne : (D.filter fun j => mv Q s j ℓ).Nonempty
  · set m := (D.filter fun j => mv Q s j ℓ).max' hne
    have hm : m ∈ D.filter fun j => mv Q s j ℓ := Finset.max'_mem _ _
    simp only [Finset.mem_filter] at hm
    refine ⟨m.succ, fun j hj => ?_⟩
    simp only [Fin.val_succ]
    constructor
    · intro hjD
      have : j ≤ m := Finset.le_max' _ _ (by simp [hjD, hj])
      rw [Fin.le_def] at this; omega
    · intro hlt
      rcases (Nat.lt_succ_iff.mp hlt).lt_or_eq with h | h
      · exact hD m hm.1 j (chain_le Q s hj hm.2 (Fin.lt_def.mpr h))
      · exact (Fin.ext h) ▸ hm.1
  · refine ⟨0, fun j hj => ?_⟩
    simp only [Fin.val_zero, Nat.not_lt_zero, iff_false]
    intro hjD
    exact hne ⟨j, by simp [hjD, hj]⟩

theorem tD_pm (s : Sex) {D : Finset (Fin Q.R)} {ℓ : Fin n} {t t' : Fin (Q.R + 1)}
    (h : IsTD Q s D ℓ t) (h' : IsTD Q s D ℓ t') : pm Q s t ℓ = pm Q s t' ℓ := by
  rcases le_total t t' with hle | hle
  · symm
    apply pm_const Q s ℓ t t' hle
    intro k a1 a2 hk
    have := (h k hk).not.mpr (by omega)
    exact this ((h' k hk).mpr a2)
  · apply pm_const Q s ℓ t' t hle
    intro k a1 a2 hk
    have := (h' k hk).not.mpr (by omega)
    exact this ((h k hk).mpr a2)

theorem tD_inj (s : Sex) {D : Finset (Fin Q.R)} (hD : IsDn Q D) {ℓ1 ℓ2 : Fin n}
    {t1 t2 : Fin (Q.R + 1)} (h1 : IsTD Q s D ℓ1 t1) (h2 : IsTD Q s D ℓ2 t2) (ht : t1 ≤ t2)
    (he : pm Q s t1 ℓ1 = pm Q s t2 ℓ2) : ℓ1 = ℓ2 := by
  classical
  by_contra hne
  set w := pm Q s t1 ℓ1 with hw
  have o1 : pm Q (opp s) t1 w = ℓ1 := by rw [pm_opp, hw]; simp
  have o2 : pm Q (opp s) t2 w = ℓ2 := by rw [pm_opp, he]; simp
  have hex := exists_step Q (opp s) w t1 t2 ht (by rw [o1, o2]; exact Ne.symm hne)
  set F := Finset.univ.filter fun k : Fin Q.R => (t1 : ℕ) ≤ k ∧ (k : ℕ) < t2 ∧ mv Q (opp s) k w
  have hF : F.Nonempty := by
    obtain ⟨k, a, b, c⟩ := hex
    exact ⟨k, by simp [F, a, b, c]⟩
  set k0 := F.min' hF
  set k1 := F.max' hF
  have hk0 : k0 ∈ F := Finset.min'_mem _ _
  have hk1 : k1 ∈ F := Finset.max'_mem _ _
  simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hk0 hk1
  have hk01 : k0 ≤ k1 := Finset.min'_le _ _ (Finset.max'_mem _ _)
  -- at `k0` the holder is `ℓ1`
  have c0 : pm Q (opp s) k0.castSucc w = ℓ1 := by
    rw [← o1]
    apply pm_const Q (opp s) w t1 k0.castSucc (Fin.le_def.mpr (by simpa using hk0.1))
    intro k a1 a2 hk
    have : k0 ≤ k := Finset.min'_le _ _ (by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a1, by have := hk0.2.1; simp at a2; omega, hk⟩)
    simp at a2; rw [Fin.le_def] at this; omega
  have m0 : mv Q s k0 ℓ1 := by
    have := (opp_mv Q s k0 w).mp hk0.2.2
    rwa [← pm_opp, c0] at this
  have n0 : k0 ∉ D := fun hD0 => by
    have := (h1 k0 m0).mp hD0
    have := hk0.1
    omega
  -- at `k1` the new holder is `ℓ2`
  have c1 : pm Q (opp s) k1.succ w = ℓ2 := by
    rw [← o2]
    symm
    apply pm_const Q (opp s) w k1.succ t2 (Fin.le_def.mpr (by simpa using hk1.2.1))
    intro k a1 a2 hk
    have : k ≤ k1 := Finset.le_max' _ _ (by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by have := hk1.1; simp at a1; omega, a2, hk⟩)
    simp at a1; rw [Fin.le_def] at this; omega
  have m1 : mv Q s k1 ℓ2 := by
    rw [mv_iff]
    intro heq
    have hm := (mv_iff Q (opp s) k1 w).mp hk1.2.2
    apply hm
    rw [c1, pm_opp]
    rw [Equiv.symm_apply_eq, heq, ← c1, pm_opp]
    simp
  have i1 : k1 ∈ D := (h2 k1 m1).mpr hk1.2.1
  rcases hk01.lt_or_eq with hl | he'
  · exact n0 (hD k1 i1 k0 (chain_le Q (opp s) hk0.2.2 hk1.2.2 hl))
  · exact n0 (he' ▸ i1)

/-- `σ` is the partner-label permutation of the canonical matching of `D` -/
def DP (s : Sex) (D : Finset (Fin Q.R)) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ ℓ t, IsTD Q s D ℓ t → σ ℓ = pm Q s t ℓ

theorem down_perm (s : Sex) {D : Finset (Fin Q.R)} (hD : IsDn Q D) :
    ∃ σ : Equiv.Perm (Fin n), DP Q s D σ := by
  choose T hT using exists_tD Q s hD
  set f : Fin n → Fin n := fun ℓ => pm Q s (T ℓ) ℓ
  have finj : Function.Injective f := by
    intro a b hab
    rcases le_total (T a) (T b) with hle | hle
    · exact tD_inj Q s hD (hT a) (hT b) hle hab
    · exact (tD_inj Q s hD (hT b) (hT a) hle hab.symm).symm
  have fbij : Function.Bijective f := Finite.injective_iff_bijective.mp finj
  refine ⟨Equiv.ofBijective f fbij, fun ℓ t ht => ?_⟩
  show pm Q s (T ℓ) ℓ = pm Q s t ℓ
  exact tD_pm Q s (hT ℓ) ht

end downperm

section dp
variable (Q : Member n) {s : Sex} {D : Finset (Fin Q.R)} {σ : Equiv.Perm (Fin n)}

theorem dp_ne (hσ : DP Q s D σ) (hD : IsDn Q D) {j : Fin Q.R} {ℓ : Fin n} (hjD : j ∈ D)
    (hj : mv Q s j ℓ) {t1 : Fin (Q.R + 1)} (ht1 : t1 ≤ j.castSucc) : σ ℓ ≠ pm Q s t1 ℓ := by
  obtain ⟨t, ht⟩ := exists_tD Q s hD ℓ
  rw [hσ ℓ t ht]
  have := (ht j hj).mp hjD
  exact norep Q s j ℓ hj t1 t ht1 (Fin.le_def.mpr (by simp; omega))

theorem dp_fix (hσ : DP Q s D σ) {ℓ : Fin n} (h : ∀ j ∈ D, ¬ mv Q s j ℓ) : σ ℓ = ℓ := by
  rw [hσ ℓ 0 (fun j hj => by simp only [Fin.val_zero, Nat.not_lt_zero, iff_false]; exact fun h' => h j h' hj),
    pm_zero]

theorem dp_mem (hσ : DP Q s D σ) {ℓ : Fin n} (h : ∃ j ∈ D, mv Q s j ℓ) :
    ∃ j ∈ D, mv Q s j (σ ℓ) := by
  by_contra hc
  push Not at hc
  have h1 : σ (σ ℓ) = σ ℓ := dp_fix Q hσ hc
  have h2 : σ ℓ = ℓ := σ.injective h1
  obtain ⟨j, hj, hm⟩ := h
  exact hc j hj (by rw [h2]; exact hm)

/-- the partner after the last step of `ℓ` in `D` -/
theorem dp_last (hσ : DP Q s D σ) (hD : IsDn Q D) {j : Fin Q.R} {ℓ : Fin n} (hjD : j ∈ D)
    (hj : mv Q s j ℓ) (hlast : ∀ k, mv Q s k ℓ → j < k → k ∉ D) : σ ℓ = pm Q s j.succ ℓ := by
  apply hσ
  intro k hk
  simp only [Fin.val_succ]
  constructor
  · intro hkD
    by_contra hc
    exact hlast k hk (Fin.lt_def.mpr (by omega)) hkD
  · intro hlt
    rcases (Nat.lt_succ_iff.mp hlt).lt_or_eq with h | h
    · exact hD j hjD k (chain_le Q s hk hj (Fin.lt_def.mpr h))
    · exact (Fin.ext h) ▸ hjD

/-- `σ` for the downset `↓k` -/
theorem dp_down_mem {k : Fin Q.R} (hσ : DP Q s (Q.down k) σ) {ℓ : Fin n} (h : ℓ ∈ Q.support k) :
    σ ℓ ∈ Q.support k := by
  rw [support_iff Q s] at h ⊢
  obtain ⟨j, hj, hm⟩ := h
  obtain ⟨j', hj', hm'⟩ := dp_mem Q hσ ⟨j, (mem_down' Q k j).mpr hj, hm⟩
  exact ⟨j', (mem_down' Q k j').mp hj', hm'⟩

theorem down_last (s : Sex) {k : Fin Q.R} {ℓ : Fin n} (_hk : mv Q s k ℓ) :
    ∀ j, mv Q s j ℓ → k < j → j ∉ Q.down k := by
  intro j hj hkj hjD
  rw [mem_down'] at hjD
  exact absurd (le_idx Q hjD) (not_le.mpr hkj)

/-- Lemma 5.1's inclusion: up to just after a step, every partner label lies in its support -/
theorem pm_mem_support (s : Sex) {k : Fin Q.R} {ℓ : Fin n} (hk : mv Q s k ℓ)
    {t : Fin (Q.R + 1)} (ht : t ≤ k.succ) : pm Q s t ℓ ∈ Q.support k := by
  classical
  by_cases hne : (Finset.univ.filter fun j : Fin Q.R => mv Q s j ℓ ∧ (j : ℕ) < t).Nonempty
  · set j := (Finset.univ.filter fun j : Fin Q.R => mv Q s j ℓ ∧ (j : ℕ) < t).max' hne
    have hj : j ∈ Finset.univ.filter fun j : Fin Q.R => mv Q s j ℓ ∧ (j : ℕ) < t :=
      Finset.max'_mem _ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have e : pm Q s t ℓ = pm Q s j.succ ℓ := by
      apply pm_const Q s ℓ j.succ t (Fin.le_def.mpr (by simp; omega))
      intro k' a1 a2 hk'
      have : k' ≤ j := Finset.le_max' _ _ (by simp [hk', a2])
      simp at a1; rw [Fin.le_def] at this; omega
    have hjk : j ≤ k := by
      have := Fin.le_def.mp ht; simp at this; rw [Fin.le_def]; omega
    have hjk' : Q.le j k := (chain_le_iff Q s hj.1 hk).mpr hjk
    obtain ⟨σ, hσ⟩ := down_perm Q s (isDn_down Q j)
    have hl := dp_last Q hσ (isDn_down Q j) ((mem_down' Q j j).mpr (le_rfl' Q j)) hj.1
      (down_last Q s hj.1)
    rw [e, ← hl]
    exact support_mono Q hjk' (dp_down_mem Q hσ (mem_support_self Q s hj.1))
  · have e : pm Q s t ℓ = pm Q s 0 ℓ := by
      apply pm_const Q s ℓ 0 t (Fin.zero_le _)
      intro k' _ a2 hk'
      exact hne ⟨k', by simp [hk', a2]⟩
    rw [e, pm_zero]
    exact mem_support_self Q s hk

end dp

section assoc
variable (Q : Member n)

theorem opp_mv_eq (s : Sex) (k : Fin Q.R) (ℓ : Fin n) :
    mv Q (opp s) k ℓ ↔ ∃ m, pm Q s k.castSucc m = ℓ ∧ mv Q s k m := by
  rw [opp_mv]
  constructor
  · intro h; exact ⟨_, by simp, h⟩
  · rintro ⟨m, rfl, hm⟩; simpa using hm

/-- the association structure `A = (p, q)`, `B = (p, x)` in the description of sex `s` -/
structure AS (s : Sex) (A : Fin Q.R) (x p q : Fin n) (B : Fin Q.R) : Prop where
  fx : Q.IsFirst x B
  fp : Q.IsFirst p A
  fq : Q.IsFirst q A
  lt : A < B
  le : Q.le A B
  pq : p ≠ q
  px : p ≠ x
  qx : q ≠ x
  mA : ∀ ℓ, mv Q s A ℓ ↔ ℓ = p ∨ ℓ = q
  mB : ∀ ℓ, mv Q s B ℓ ↔ ℓ = p ∨ ℓ = x
  gap : ∀ k, A < k → k < B → ¬ mv Q s k p
  pA1 : pm Q s A.succ p = q
  pA2 : pm Q s A.succ q = p
  pB1 : pm Q s B.succ p = x
  pB2 : pm Q s B.succ x = q
  supB : Q.support B = {p, q, x}

theorem pm_man (t : Fin (Q.R + 1)) (ℓ : Fin n) : pm Q .man t ℓ = (Q.μ 0).symm (Q.μ t ℓ) := rfl

theorem pm_woman (t : Fin (Q.R + 1)) : pm Q .woman t = (pm Q .man t).symm := rfl

theorem as_of_assoc {A : Fin Q.R} {x y z : Fin n} {B : Fin Q.R} (hs : Assoc Q A x y z B) :
    AS Q .man A x y z B ∧ AS Q .woman A x z y B := by
  have hP := assoc_partners Q hs
  have hxB := hs.1
  have hexc := hs.2.1
  obtain ⟨-, -, hAB, hyz, hyx, hzx, hpA, hyA, hzA, hdown, hpB, hgap⟩ := hs
  have hle : Q.le A B := by
    have : A ∈ Q.down B := by rw [hdown]; simp
    exact (mem_down' Q B A).mp this
  have mA : ∀ ℓ, mv Q .man A ℓ ↔ ℓ = y ∨ ℓ = z := by
    intro ℓ
    show Q.moves .man A ℓ ↔ _
    rw [← mem_participants, hpA]; simp
  have mB : ∀ ℓ, mv Q .man B ℓ ↔ ℓ = y ∨ ℓ = x := by
    intro ℓ
    show Q.moves .man B ℓ ↔ _
    rw [← mem_participants, hpB]; simp
  have hzA' : Q.μ A.succ z = Q.μ 0 y := by
    rw [swap_eq Q A z y (by rw [hpA, Finset.pair_comm]) hyz.symm, hP.1]
  have sub : ({y, z, x} : Finset (Fin n)) ⊆ Q.support B := by
    intro ℓ hℓ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hℓ
    rcases hℓ with rfl | rfl | rfl
    · exact mem_support_self Q .man ((mB ℓ).mpr (Or.inl rfl))
    · exact support_mono Q hle (mem_support_self Q .man ((mA ℓ).mpr (Or.inr rfl)))
    · exact mem_support_self Q .man ((mB ℓ).mpr (Or.inr rfl))
  have supB : Q.support B = {y, z, x} := by
    symm
    apply Finset.eq_of_subset_of_card_le sub
    have : Q.s B = 3 := hexc.2
    unfold Member.s at this
    rw [this, Finset.card_insert_of_notMem (by simp [hyz, hyx]),
      Finset.card_pair hzx]
  -- partners along the men's chain
  have pA1 : pm Q .man A.succ y = z := by rw [pm_man, hP.2.2.1]; simp
  have pA2 : pm Q .man A.succ z = y := by rw [pm_man, hzA']; simp
  have pB1 : pm Q .man B.succ y = x := by rw [pm_man, hP.2.2.2.2.2.1]; simp
  have pB2 : pm Q .man B.succ x = z := by rw [pm_man, hP.2.2.2.2.2.2]; simp
  have cA1 : pm Q .man A.castSucc y = y := by rw [pm_man, hP.1]; simp
  have cA2 : pm Q .man A.castSucc z = z := by rw [pm_man, hP.2.1]; simp
  have cB1 : pm Q .man B.castSucc y = z := by rw [pm_man, hP.2.2.2.1]; simp
  have cB2 : pm Q .man B.castSucc x = x := by rw [pm_man, hP.2.2.2.2.1]; simp
  refine ⟨⟨hxB, hyA, hzA, hAB, hle, hyz, hyx, hzx, mA, mB, hgap, pA1, pA2, pB1, pB2, supB⟩,
    ⟨hxB, hzA, hyA, hAB, hle, hyz.symm, hzx, hyx, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro ℓ
    rw [show Sex.woman = opp .man from rfl, opp_mv_eq]
    constructor
    · rintro ⟨m, rfl, hm⟩
      rcases (mA m).mp hm with rfl | rfl
      · rw [cA1]; exact Or.inr rfl
      · rw [cA2]; exact Or.inl rfl
    · rintro (h | h)
      · exact ⟨z, by rw [cA2, h], (mA z).mpr (Or.inr rfl)⟩
      · exact ⟨y, by rw [cA1, h], (mA y).mpr (Or.inl rfl)⟩
  · intro ℓ
    rw [show Sex.woman = opp .man from rfl, opp_mv_eq]
    constructor
    · rintro ⟨m, rfl, hm⟩
      rcases (mB m).mp hm with rfl | rfl
      · rw [cB1]; exact Or.inl rfl
      · rw [cB2]; exact Or.inr rfl
    · rintro (h | h)
      · exact ⟨y, by rw [cB1, h], (mB y).mpr (Or.inl rfl)⟩
      · exact ⟨x, by rw [cB2, h], (mB x).mpr (Or.inr rfl)⟩
  · intro k h1 h2 hk
    rw [show Sex.woman = opp .man from rfl, opp_mv_eq] at hk
    obtain ⟨m, hm1, hm2⟩ := hk
    have hc : pm Q .man k.castSucc y = z := by
      rw [← pA1]
      apply pm_const Q .man y A.succ k.castSucc (lt_succ_le h1)
      intro k' a1 a2
      exact hgap k' (lt_of_succ_le a1) (lt_trans (lt_of_castSucc a2) h2)
    have : m = y := (pm Q .man k.castSucc).injective (hm1.trans hc.symm)
    rw [this] at hm2
    exact hgap k h1 h2 hm2
  · rw [pm_woman, Equiv.symm_apply_eq, pA1]
  · rw [pm_woman, Equiv.symm_apply_eq, pA2]
  · rw [pm_woman, Equiv.symm_apply_eq, pB2]
  · rw [pm_woman, Equiv.symm_apply_eq, pB1]
  · rw [supB]; ext ℓ; simp; tauto

theorem as_of_XA {A : Fin Q.R} {x : Fin n} (hx : x ∈ Q.XA A) (s : Sex) :
    ∃ p q B, AS Q s A x p q B ∧ Assoc Q A x p q B ∨ AS Q s A x p q B ∧ Assoc Q A x q p B := by
  obtain ⟨y, z, B, hs⟩ := assoc_of_XA Q A x hx
  obtain ⟨h1, h2⟩ := as_of_assoc Q hs
  cases s
  · exact ⟨y, z, B, Or.inl ⟨h1, hs⟩⟩
  · exact ⟨z, y, B, Or.inr ⟨h2, hs⟩⟩

end assoc

end Dev.L83
end StableCount
end

section
set_option autoImplicit false

namespace StableCount
open StableMatching
namespace Dev.L83
open Dev.L52 Dev.L62

variable {n : ℕ}

section tools
variable (Q : Member n)

theorem rank_eq (s : Sex) (ℓ : Fin n) (i : Fin Q.R) :
    Q.rank s (Q.person s ℓ) i = (Finset.univ.filter fun j => mv Q s j ℓ ∧ j ≤ i).card := by
  unfold Member.rank Member.chainOf
  rw [Finset.filter_filter]
  rfl

theorem dL_eq (s : Sex) (ℓ : Fin n) :
    Q.dL s ℓ = (Finset.univ.filter fun j => mv Q s j ℓ).card := rfl

theorem rank_first (s : Sex) {ℓ : Fin n} {B : Fin Q.R} (h : Q.IsFirst ℓ B) :
    Q.rank s (Q.person s ℓ) B = 1 := by
  obtain ⟨hv, rfl⟩ := h
  exact first_rank Q s ℓ hv

theorem rank_mono (s : Sex) {ℓ : Fin n} {a b : Fin Q.R} (hb : mv Q s b ℓ) (hab : a < b) :
    Q.rank s (Q.person s ℓ) a < Q.rank s (Q.person s ℓ) b := by
  rw [rank_eq, rank_eq]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨b, by simp [hb], by simp [hab]⟩
  · intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun h => ⟨h.1, h.2.trans hab.le⟩

/-- the step of rank `r + 1` just after the step `a` of rank `r` -/
theorem next_of_rank (s : Sex) {ℓ : Fin n} {a b : Fin Q.R} (ha : mv Q s a ℓ) (hb : mv Q s b ℓ)
    (hr : Q.rank s (Q.person s ℓ) b = Q.rank s (Q.person s ℓ) a + 1) :
    a < b ∧ ∀ k, a < k → k < b → ¬ mv Q s k ℓ := by
  have hab : a < b := by
    by_contra h
    rcases (not_lt.mp h).lt_or_eq with h | h
    · have := rank_mono Q s ha h; omega
    · rw [h] at hr; omega
  refine ⟨hab, fun k h1 h2 hk => ?_⟩
  have i1 := rank_mono Q s hk h1
  have i2 := rank_mono Q s hb h2
  omega

theorem rank_le_dL (s : Sex) (ℓ : Fin n) (i : Fin Q.R) :
    Q.rank s (Q.person s ℓ) i ≤ Q.dL s ℓ := by
  rw [rank_eq, dL_eq]
  apply Finset.card_le_card
  intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact fun h => h.1

/-- Lemma 5.1 -/
theorem l51 (s : Sex) {ℓ : Fin n} {i : Fin Q.R} (hi : mv Q s i ℓ) :
    Q.rank s (Q.person s ℓ) i + 1 ≤ Q.s i := by
  classical
  set S := Finset.univ.filter fun j => mv Q s j ℓ ∧ j ≤ i
  set T : Finset (Fin (Q.R + 1)) := insert 0 (S.image Fin.succ)
  have hT : T.card = S.card + 1 := by
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ (Fin.succ_injective _)]
    simp only [Finset.mem_image, not_exists, not_and]
    intro j _ h; exact Fin.succ_ne_zero j h
  rw [rank_eq]
  rw [← hT]
  unfold Member.s
  apply Finset.card_le_card_of_injOn (fun t => pm Q s t ℓ)
  · intro t ht
    simp only [T, Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image,
      Finset.mem_coe] at ht
    apply pm_mem_support Q s hi
    rcases ht with rfl | ⟨j, hj, rfl⟩
    · exact Fin.zero_le _
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact Fin.succ_le_succ_iff.mpr hj.2
  · have key : ∀ t1 ∈ T, ∀ t2 ∈ T, t1 < t2 → pm Q s t2 ℓ ≠ pm Q s t1 ℓ := by
      intro t1 h1 t2 h2 hlt
      simp only [T, Finset.mem_insert, Finset.mem_image] at h1 h2
      rcases h2 with rfl | ⟨j2, hj2, rfl⟩
      · exact absurd hlt (not_lt.mpr (Fin.zero_le _))
      · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj2
        apply norep Q s j2 ℓ hj2.1 t1 j2.succ _ (le_refl _)
        rcases h1 with rfl | ⟨j1, _, rfl⟩
        · exact Fin.zero_le _
        · exact lt_succ_le (Fin.succ_lt_succ_iff.mp hlt)
    intro t1 h1 t2 h2 he
    rcases lt_trichotomy t1 t2 with hl | hl | hl
    · exact absurd he.symm (key t1 h1 t2 h2 hl)
    · exact hl
    · exact absurd he (key t2 h2 t1 h1 hl)

theorem exists_mv (s : Sex) (k : Fin Q.R) : ∃ ℓ, mv Q s k ℓ := by
  by_contra hc
  push Not at hc
  have e : pm Q s k.castSucc = pm Q s k.succ := Equiv.ext fun ℓ => by
    have := hc ℓ; rwa [mv_iff, not_not] at this
  have e' : pm Q .man k.castSucc = pm Q .man k.succ := by
    cases s
    · exact e
    · have := congrArg Equiv.symm e
      simpa [pm_woman] using this
  apply (step_lt Q k).2
  ext m
  have := congrArg (fun σ => σ m) e'
  simp only [pm_man] at this
  rw [(Q.μ 0).symm.injective this]

/-- a mover's new partner was held by another mover -/
theorem new_from' (s : Sex) {k : Fin Q.R} {ℓ : Fin n} (hℓ : mv Q s k ℓ) :
    ∃ m, m ≠ ℓ ∧ mv Q s k m ∧ pm Q s k.succ ℓ = pm Q s k.castSucc m := by
  set m := (pm Q s k.castSucc).symm (pm Q s k.succ ℓ)
  have hm : pm Q s k.castSucc m = pm Q s k.succ ℓ := by simp [m]
  have hne : m ≠ ℓ := by
    intro h; rw [h] at hm; exact ((mv_iff Q s k ℓ).mp hℓ) hm
  refine ⟨m, hne, ?_, hm.symm⟩
  rw [mv_iff]
  intro h
  exact hne ((pm Q s k.succ).injective (h.symm.trans hm))

theorem exists_two_mv (s : Sex) (k : Fin Q.R) : ∃ a b, a ≠ b ∧ mv Q s k a ∧ mv Q s k b := by
  obtain ⟨ℓ, hℓ⟩ := exists_mv Q s k
  obtain ⟨m, hne, hm, -⟩ := new_from' Q s hℓ
  exact ⟨m, ℓ, hne, hm, hℓ⟩

end tools

section tools2
variable (Q : Member n)

theorem mem_down_iff (k j : Fin Q.R) : j ∈ Q.down k ↔ Q.le j k := mem_down' Q k j

/-- three labels -/
theorem mem3 {p q x m : Fin n} (h : m ∈ ({p, q, x} : Finset (Fin n))) : m = p ∨ m = q ∨ m = x := by
  simpa using h

theorem mem4 {p q x y m : Fin n} (h : m ∈ ({p, q, x, y} : Finset (Fin n))) :
    m = p ∨ m = q ∨ m = x ∨ m = y := by
  simpa using h

theorem card3 {p q x : Fin n} (h1 : p ≠ q) (h2 : p ≠ x) (h3 : q ≠ x) :
    ({p, q, x} : Finset (Fin n)).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [h1, h2]), Finset.card_pair h3]

theorem card4 {p q x y : Fin n} (h1 : p ≠ q) (h2 : p ≠ x) (h3 : p ≠ y) (h4 : q ≠ x) (h5 : q ≠ y)
    (h6 : x ≠ y) : ({p, q, x, y} : Finset (Fin n)).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [h1, h2, h3]), card3 h4 h5 h6]

end tools2

section AS
variable {Q : Member n} {s : Sex} {A B : Fin Q.R} {x p q : Fin n}

theorem AS.mvA1 (h : AS Q s A x p q B) : mv Q s A p := (h.mA p).mpr (Or.inl rfl)
theorem AS.mvA2 (h : AS Q s A x p q B) : mv Q s A q := (h.mA q).mpr (Or.inr rfl)
theorem AS.mvB1 (h : AS Q s A x p q B) : mv Q s B p := (h.mB p).mpr (Or.inl rfl)
theorem AS.mvB2 (h : AS Q s A x p q B) : mv Q s B x := (h.mB x).mpr (Or.inr rfl)

theorem AS.x_first (h : AS Q s A x p q B) : ∀ k, k < B → ¬ mv Q s k x :=
  (isFirst_mv Q s h.fx).2

theorem AS.pSB (h : AS Q s A x p q B) : p ∈ Q.support B := by rw [h.supB]; simp
theorem AS.qSB (h : AS Q s A x p q B) : q ∈ Q.support B := by rw [h.supB]; simp

/-- each parent has at most one exceptional label -/
theorem AS.unique {x' q' : Fin n} {B' : Fin Q.R} (h : AS Q s A x p q B) (h' : AS Q s A x' p q' B') :
    x = x' ∧ B = B' := by
  have hBB : B = B' := by
    rcases lt_trichotomy B B' with hl | he | hl
    · exact absurd h.mvB1 (h'.gap B h.lt hl)
    · exact he
    · exact absurd h'.mvB1 (h.gap B' h'.lt hl)
  subst hBB
  refine ⟨?_, rfl⟩
  rcases (h.mB x').mp h'.mvB2 with e | e
  · exact absurd e.symm h'.px
  · exact e.symm

/-- the first rotation of `x` lies below every rotation whose support contains `x` -/
theorem AS.B_le (h : AS Q s A x p q B) {k : Fin Q.R} (hk : x ∈ Q.support k) : Q.le B k := by
  rw [support_iff Q s] at hk
  obtain ⟨j, hj, hm⟩ := hk
  have hBj : B ≤ j := not_lt.mp fun hl => h.x_first j hl hm
  exact le_tr Q ((chain_le_iff Q s h.mvB2 hm).mpr hBj) hj

theorem AS.supB_le (h : AS Q s A x p q B) {k : Fin Q.R} (hk : x ∈ Q.support k) :
    ({p, q, x} : Finset (Fin n)) ⊆ Q.support k := by
  rw [← h.supB]; exact support_mono Q (h.B_le hk)

theorem AS.card (h : AS Q s A x p q B) : ({p, q, x} : Finset (Fin n)).card = 3 :=
  card3 h.pq h.px h.qx

end AS

section P1
variable (Q : Member n) {s : Sex} {A B : Fin Q.R} {x p q : Fin n}

/-- Lemma 5.5 (i) -/
theorem P1 (h : AS Q s A x p q B) {C : Fin Q.R} (hxC : mv Q s C x) (hBC : B < C) : 4 ≤ Q.s C := by
  have hle : Q.le B C := chain_le Q s h.mvB2 hxC hBC
  have sub := h.supB_le (mem_support_self Q s hxC)
  by_contra hc
  have heq : Q.support C = {p, q, x} := by
    symm; apply Finset.eq_of_subset_of_card_le sub
    rw [h.card]; unfold Member.s at hc; omega
  obtain ⟨σ, hσ⟩ := down_perm Q s (isDn_down Q C)
  have hD := isDn_down Q C
  have AD : A ∈ Q.down C := (mem_down_iff Q C A).mpr (le_tr Q h.le hle)
  have BD : B ∈ Q.down C := (mem_down_iff Q C B).mpr hle
  have CD : C ∈ Q.down C := (mem_down_iff Q C C).mpr (le_rfl' Q C)
  have inK : ∀ m, m ∈ Q.support C → m = p ∨ m = q ∨ m = x := fun m hm => by
    rw [heq] at hm; exact mem3 hm
  have Sx : x ∈ Q.support C := by rw [heq]; simp
  have Sp : p ∈ Q.support C := by rw [heq]; simp
  have Sq : q ∈ Q.support C := by rw [heq]; simp
  -- σ x = p
  have x1 : σ x ≠ x := by
    have := dp_ne Q hσ hD BD h.mvB2 (Fin.zero_le _); rwa [pm_zero] at this
  have x2 : σ x ≠ q := by
    have := dp_ne Q hσ hD CD hxC (t1 := B.succ) (lt_succ_le hBC); rwa [h.pB2] at this
  have sx : σ x = p := by
    rcases inK _ (dp_down_mem Q hσ Sx) with e | e | e
    · exact e
    · exact absurd e x2
    · exact absurd e x1
  have p1 : σ p ≠ p := by
    have := dp_ne Q hσ hD AD h.mvA1 (Fin.zero_le _); rwa [pm_zero] at this
  have p2 : σ p ≠ q := by
    have := dp_ne Q hσ hD BD h.mvB1 (t1 := A.succ) (lt_succ_le h.lt); rwa [h.pA1] at this
  have sp : σ p = x := by
    rcases inK _ (dp_down_mem Q hσ Sp) with e | e | e
    · exact absurd e p1
    · exact absurd e p2
    · exact e
  have q1 : σ q ≠ q := by
    have := dp_ne Q hσ hD AD h.mvA2 (Fin.zero_le _); rwa [pm_zero] at this
  rcases inK _ (dp_down_mem Q hσ Sq) with e | e | e
  · exact h.qx (σ.injective (e.trans sx.symm))
  · exact q1 e
  · exact h.pq (σ.injective (sp.trans e.symm))

end P1

section P34
variable (Q : Member n) {s : Sex} {A B : Fin Q.R} {x p q : Fin n}

end P34

section P3
variable (Q : Member n) {s : Sex} {A B : Fin Q.R} {x p q : Fin n}

end P3

section P5
variable (Q : Member n) {s : Sex} {A B : Fin Q.R} {x p q : Fin n}

end P5

section P6
variable (Q : Member n) {s : Sex} {A B E : Fin Q.R} {x y p q : Fin n}

end P6

section groups
variable (Q : Member n)

theorem mem_fg {G : Fin Q.R} {w : Fin n} : w ∈ Q.firstGroup G ↔ Q.IsFirst w G := by
  simp [Member.firstGroup]

theorem single_s3 {G : Fin Q.R} {z : Fin n} (hfg : Q.firstGroup G = {z}) : 3 ≤ Q.s G := by
  have hzG : Q.IsFirst z G := (mem_fg Q).mp (by rw [hfg]; simp)
  obtain ⟨mz, nz⟩ := isFirst_mv Q .man hzG
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_mv Q .man G
  obtain ⟨m, hm, hmz⟩ : ∃ m, mv Q .man G m ∧ m ≠ z := by
    by_cases e : a = z
    · exact ⟨b, hb, fun e2 => hab (e.trans e2.symm)⟩
    · exact ⟨a, ha, e⟩
  obtain ⟨f, hf, hfG⟩ := exists_first Q .man hm
  have hfG' : f < G := by
    refine lt_of_le_of_ne hfG fun e => hmz ?_
    have : m ∈ Q.firstGroup G := (mem_fg Q).mpr (e ▸ hf)
    rw [hfg] at this; simpa using this
  have fleG : Q.le f G := chain_le Q .man (isFirst_mv Q .man hf).1 hm hfG'
  obtain ⟨c, d, hcd, hc, hd⟩ := exists_two_mv Q .man f
  obtain ⟨m', hm', hm'm⟩ : ∃ m', mv Q .man f m' ∧ m' ≠ m := by
    by_cases e : c = m
    · exact ⟨d, hd, fun e2 => hcd (e.trans e2.symm)⟩
    · exact ⟨c, hc, e⟩
  have hm'z : m' ≠ z := fun e => nz f hfG' (e ▸ hm')
  have sub : ({z, m, m'} : Finset (Fin n)) ⊆ Q.support G := by
    intro w hw
    rcases mem3 hw with e | e | e <;> rw [e]
    · exact mem_support_self Q .man mz
    · exact mem_support_self Q .man hm
    · exact support_mono Q fleG (mem_support_self Q .man hm')
  have := Finset.card_le_card sub
  rw [card3 hmz.symm hm'z.symm hm'm.symm] at this
  exact this

theorem not_initial {G : Fin Q.R} {z : Fin n} (hfg : Q.firstGroup G = {z}) :
    ¬ Q.IsInitialSwap G := by
  intro hI
  have sub : Q.participants G ⊆ Q.firstGroup G := fun w hw => (mem_fg Q).mpr (hI.2 w hw)
  have := Finset.card_le_card sub
  rw [hI.1, hfg] at this; simp at this

theorem fgA {s : Sex} {A B : Fin Q.R} {x p q : Fin n} (h : AS Q s A x p q B) :
    Q.firstGroup A = {p, q} := by
  ext w
  rw [mem_fg]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hw; exact (h.mA w).mp (isFirst_mv Q s hw).1
  · rintro (e | e) <;> rw [e]
    · exact h.fp
    · exact h.fq

/-- a singleton first group of size `≠ 3` support that is not exceptional: an ordinary rotation with
support at least four -/
theorem single_ord {G : Fin Q.R} {z : Fin n} (hfg : Q.firstGroup G = {z})
    (hne : ¬ Q.IsExceptional z) : Q.IsOrdinary G ∧ 4 ≤ Q.s G := by
  have hzG : Q.IsFirst z G := (mem_fg Q).mp (by rw [hfg]; simp)
  have nexc : ¬ Q.IsExceptionalSwap G := fun he => hne ⟨G, hzG, he⟩
  refine ⟨⟨⟨z, by rw [hfg]; simp⟩, not_initial Q hfg, nexc⟩, ?_⟩
  have := single_s3 Q hfg
  rcases this.lt_or_eq with h4 | h3
  · omega
  · exact absurd ⟨by rw [hfg]; simp, h3.symm⟩ nexc

/-- members of `Z_A` for `A ∈ 𝒫₀`: a singleton first group with support a triple plus itself -/
theorem za_struct {s : Sex} {A B : Fin Q.R} {x p q : Fin n} (h : AS Q s A x p q B)
    (hAI : Q.IsInitialSwap A) {z : Fin n} {G : Fin Q.R} (hzG : Q.IsFirst z G)
    (hord : Q.IsOrdinary G) (hS : ({p, q, x} : Finset (Fin n)) ⊆ Q.support G) (h5 : Q.s G < 5)
    (hexcB : Q.IsExceptionalSwap B) :
    Q.firstGroup G = {z} ∧ Q.support G = {p, q, x, z} := by
  obtain ⟨mz, -⟩ := isFirst_mv Q s hzG
  have hGA : G ≠ A := fun e => hord.2.1 (e ▸ hAI)
  have hGB : G ≠ B := fun e => hord.2.2 (e ▸ hexcB)
  have hzp : z ≠ p := fun e => hGA (isFirst_unique Q hzG (e ▸ h.fp))
  have hzq : z ≠ q := fun e => hGA (isFirst_unique Q hzG (e ▸ h.fq))
  have hzx : z ≠ x := fun e => hGB (isFirst_unique Q hzG (e ▸ h.fx))
  have sub : ({p, q, x, z} : Finset (Fin n)) ⊆ Q.support G := by
    intro w hw
    rcases mem4 hw with e | e | e | e
    · exact hS (by rw [e]; simp)
    · exact hS (by rw [e]; simp)
    · exact hS (by rw [e]; simp)
    · rw [e]; exact mem_support_self Q s mz
  have hc := card4 h.pq h.px hzp.symm h.qx hzq.symm hzx.symm
  have heq : Q.support G = {p, q, x, z} := by
    symm; apply Finset.eq_of_subset_of_card_le sub
    rw [hc]; unfold Member.s at h5; omega
  refine ⟨?_, heq⟩
  ext w
  rw [mem_fg, Finset.mem_singleton]
  constructor
  · intro hw
    have wS := mem_support_self Q s (isFirst_mv Q s hw).1
    rw [heq] at wS
    rcases mem4 wS with e | e | e | e
    · rw [e] at hw; exact absurd (isFirst_unique Q hw h.fp) hGA
    · rw [e] at hw; exact absurd (isFirst_unique Q hw h.fq) hGA
    · rw [e] at hw; exact absurd (isFirst_unique Q hw h.fx) hGB
    · exact e
  · intro e; rw [e]; exact hzG

end groups

end Dev.L83
end StableCount
end

section
set_option autoImplicit false

namespace StableCount
open StableMatching
namespace Dev.L83
open Dev.L52 Dev.L62

variable {n : ℕ}

section terms
variable (Q : Member n) (h : ℕ → ℝ)

theorem as_XA {A : Fin Q.R} {x : Fin n} (hx : x ∈ Q.XA A) (s : Sex) :
    ∃ p q B, AS Q s A x p q B := by
  obtain ⟨p, q, B, H⟩ := as_of_XA Q hx s
  rcases H with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact ⟨p, q, B, h1⟩

theorem exc_B {s : Sex} {A B : Fin Q.R} {x p q : Fin n} (hAS : AS Q s A x p q B)
    (hx : x ∈ Q.XA A) : Q.IsExceptionalSwap B := by
  simp only [Member.XA, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨⟨i, hi, he⟩, -⟩ := hx
  rw [isFirst_unique Q hi hAS.fx] at he
  exact he

theorem Ex_term_nonneg (hh : IsAdmissible h) {A : Fin Q.R} {x : Fin n} (hx : x ∈ Q.XA A)
    (s : Sex) : ∀ i ∈ (Q.chainOf s (Q.person s x)).filter
      (fun i => 2 ≤ Q.rank s (Q.person s x) i ∧ Q.rank s (Q.person s x) i ≤ 3),
      0 ≤ ((Q.s i : ℝ) - 4) * h (Q.rank s (Q.person s x) i) := by
  obtain ⟨p, q, B, hAS⟩ := as_XA Q hx s
  intro i hi
  simp only [Finset.mem_filter] at hi
  obtain ⟨hic, h2, h3⟩ := hi
  have hmi : mv Q s i x := (mem_chainOf Q s _ i).mp hic
  have hp := hpos hh (show 1 ≤ Q.rank s (Q.person s x) i by omega)
  have hs4 : 4 ≤ Q.s i := by
    rcases (show Q.rank s (Q.person s x) i = 2 ∨ Q.rank s (Q.person s x) i = 3 by omega) with e | e
    · have hr1 := rank_first Q s hAS.fx
      obtain ⟨hBi, -⟩ := next_of_rank Q s hAS.mvB2 hmi (by rw [e, hr1])
      exact P1 Q hAS hmi hBi
    · have := l51 Q s hmi; omega
  have : (4 : ℝ) ≤ Q.s i := by exact_mod_cast hs4
  exact mul_nonneg (by linarith) hp.le

theorem Ex_nonneg (hh : IsAdmissible h) {A : Fin Q.R} {x : Fin n} (hx : x ∈ Q.XA A) (s : Sex) :
    0 ≤ Q.Ex h s x :=
  Finset.sum_nonneg (Ex_term_nonneg Q h hh hx s)

/-- the first group of an ordinary singleton -/
theorem beta_single {G : Fin Q.R} {z : Fin n} (hzG : Q.IsFirst z G) (hfg : Q.firstGroup G = {z})
    (hord : Q.IsOrdinary G) (s : Sex) :
    Q.beta h s z = Hsum h (Q.dL s z) + 2 * h 1 + (if 2 ≤ Q.dL s z then h 2 else 0) := by
  have c1 : ∃ i, Q.IsFirst z i ∧ Q.IsOrdinary i := ⟨G, hzG, hord⟩
  have c2 : ¬ ∃ i, Q.IsFirst z i ∧ 3 ≤ (Q.firstGroup i).card := by
    rintro ⟨i, hi, h3⟩
    rw [isFirst_unique Q hi hzG, hfg] at h3; simp at h3
  simp only [Member.beta]
  rw [if_pos c1, if_neg c2]

theorem down_chain_single {s : Sex} {G : Fin Q.R} {z : Fin n} (hzG : Q.IsFirst z G) :
    (Q.down G ∩ Q.chainOf s (Q.person s z)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨G, ?_⟩
  ext j
  simp only [Finset.mem_inter, mem_down', Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    have hm : mv Q s j z := (mem_chainOf Q s _ j).mp h2
    have hGj : G ≤ j := not_lt.mp fun hl => (isFirst_mv Q s hzG).2 j hl hm
    exact le_antisymm (le_idx Q h1) hGj
  · rintro rfl
    exact ⟨le_rfl' Q _, (mem_chainOf Q s _ _).mpr (isFirst_mv Q s hzG).1⟩

theorem pLoss_ge_z (hh : IsAdmissible h) {s : Sex} {G : Fin Q.R} {z : Fin n}
    (hzG : Q.IsFirst z G) : h (Q.dL s z) ≤ Q.pLoss h s G ∧ 1 ≤ Q.dL s z := by
  have hnn : ∀ r, 1 ≤ r → 0 ≤ h r := fun r hr => (hpos hh hr).le
  obtain ⟨e, d1⟩ := tm_one Q h s G z (down_chain_single Q hzG)
  refine ⟨?_, d1⟩
  rw [← e, pLoss_eq]
  exact Finset.single_le_sum (f := tm Q h s G) (fun v _ => tm_nonneg Q h hnn s G v)
    (Finset.mem_univ z)

/-- the rank-two terms of `T_z` -/
theorem T2_term_nonneg {s : Sex} {G : Fin Q.R} {z : Fin n} (hzG : Q.IsFirst z G) (h4 : 4 ≤ Q.s G)
    (hh : IsAdmissible h) :
    ∀ i ∈ (Q.chainOf s (Q.person s z)).filter (fun i => Q.rank s (Q.person s z) i = 2),
      0 ≤ h 2 * ((Q.s i : ℝ) - 4) := by
  intro i hi
  simp only [Finset.mem_filter] at hi
  have hmi : mv Q s i z := (mem_chainOf Q s _ i).mp hi.1
  obtain ⟨hGi, -⟩ := next_of_rank Q s (isFirst_mv Q s hzG).1 hmi
    (by rw [hi.2, rank_first Q s hzG])
  have hle := support_mono Q (chain_le Q s (isFirst_mv Q s hzG).1 hmi hGi)
  have := Finset.card_le_card hle
  have h4' : (4 : ℝ) ≤ Q.s i := by
    have : 4 ≤ Q.s i := le_trans h4 this
    exact_mod_cast this
  have p2 := hpos hh (show 1 ≤ 2 by norm_num)
  exact mul_nonneg p2.le (by linarith)

/-- `T_z` for an ordinary singleton `{z}` with first rotation `G` -/
theorem Tz_eq {s : Sex} {G : Fin Q.R} {z : Fin n} (hzG : Q.IsFirst z G)
    (hfg : Q.firstGroup G = {z}) (hord : Q.IsOrdinary G) :
    Q.Tz h s z = Hsum h (Q.dL s z) + 2 * h 1 + (if 2 ≤ Q.dL s z then h 2 else 0) -
      lam (Q.pLoss h s G) + ∑ i ∈ (Q.chainOf s (Q.person s z)).filter
        (fun i => Q.rank s (Q.person s z) i = 2), h 2 * ((Q.s i : ℝ) - 4) := by
  unfold Member.Tz
  rw [atFirst_eq Q hzG]
  unfold Member.Delta
  rw [hfg, Finset.sum_singleton, Finset.card_singleton, beta_single Q h hzG hfg hord]
  push_cast
  ring

theorem Tz_nonneg (hh : IsAdmissible h) {s : Sex} {G : Fin Q.R} {z : Fin n} (hzG : Q.IsFirst z G)
    (hfg : Q.firstGroup G = {z}) (hord : Q.IsOrdinary G) (h4 : 4 ≤ Q.s G) : 0 ≤ Q.Tz h s z := by
  rw [Tz_eq Q h hzG hfg hord]
  obtain ⟨hp, hd⟩ := pLoss_ge_z Q h hh (s := s) hzG
  have := delta_nonneg hh hd hp
  have := Finset.sum_nonneg (T2_term_nonneg Q h hzG h4 hh (s := s))
  linarith

end terms

section main
variable (Q : Member n) (h : ℕ → ℝ)

theorem P0_spec {A : Fin Q.R} (hA : A ∈ Q.P0) : Q.IsInitialSwap A ∧
    ∀ i, Q.IsOrdinary i → Q.HasTripleIn A (Q.support i) → Q.s i < 5 := by
  simp only [Member.P0, Finset.mem_sdiff, Member.initialSwaps, Member.P5, Finset.mem_filter,
    Finset.mem_univ, true_and] at hA
  refine ⟨hA.1, fun i ho ht => ?_⟩
  by_contra hc
  exact hA.2 ⟨hA.1, i, ho, by omega, ht⟩

theorem init_s2 {i : Fin Q.R} (hI : Q.IsInitialSwap i) : Q.s i ≤ 2 := by
  obtain ⟨a, b, hab, hp⟩ := Finset.card_eq_two.mp hI.1
  have ha : Q.IsFirst a i := hI.2 a (by rw [hp]; simp)
  have hb : Q.IsFirst b i := hI.2 b (by rw [hp]; simp)
  have hd := down_initial Q i a b hp ha hb
  have sub : Q.support i ⊆ Q.participants i := by
    intro ℓ hℓ
    rw [support_iff Q .man] at hℓ
    obtain ⟨j, hj, hm⟩ := hℓ
    have : j ∈ Q.down i := (mem_down' Q i j).mpr hj
    rw [hd, Finset.mem_singleton] at this
    rw [this] at hm
    exact (mem_participants Q i ℓ).mpr hm
  have := Finset.card_le_card sub
  rw [hI.1] at this
  exact this

theorem ZA_spec {A : Fin Q.R} (hAI : Q.IsInitialSwap A)
    (hP0 : ∀ i, Q.IsOrdinary i → Q.HasTripleIn A (Q.support i) → Q.s i < 5) {z : Fin n}
    (hz : z ∈ Q.ZA A) : ∃ G, Q.IsFirst z G ∧ Q.IsOrdinary G ∧ Q.firstGroup G = {z} ∧
      4 ≤ Q.s G ∧ Q.HasTripleIn A (Q.support G) := by
  simp only [Member.ZA, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  obtain ⟨G, hzG, hord, htr⟩ := hz
  obtain ⟨x, hxX, hsub⟩ := htr
  obtain ⟨p, q, B, hAS⟩ := as_XA Q hxX .man
  rw [fgA Q hAS] at hsub
  have hS : ({p, q, x} : Finset (Fin n)) ⊆ Q.support G := by
    intro w hw; apply hsub
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw ⊢; tauto
  obtain ⟨fg, -⟩ := za_struct Q hAS hAI hzG hord hS (hP0 G hord ⟨x, hxX, by
    rw [fgA Q hAS]; exact hsub⟩) (exc_B Q hAS hxX)
  have hne : ¬ Q.IsExceptional z := by
    rintro ⟨i, hi, he⟩
    rw [isFirst_unique Q hi hzG] at he
    exact hord.2.2 he
  exact ⟨G, hzG, hord, fg, (single_ord Q fg hne).2, ⟨x, hxX, by rw [fgA Q hAS]; exact hsub⟩⟩

theorem Tz_nonneg' (hh : IsAdmissible h) {A : Fin Q.R} (hAI : Q.IsInitialSwap A)
    (hP0 : ∀ i, Q.IsOrdinary i → Q.HasTripleIn A (Q.support i) → Q.s i < 5) (s : Sex)
    {z : Fin n} (hz : z ∈ Q.ZA A) : 0 ≤ Q.Tz h s z := by
  obtain ⟨G, hzG, hord, fg, h4, -⟩ := ZA_spec Q hAI hP0 hz
  exact Tz_nonneg Q h hh hzG fg hord h4

theorem RA_ge (hh : IsAdmissible h) {A : Fin Q.R} (hAI : Q.IsInitialSwap A)
    (hP0 : ∀ i, Q.IsOrdinary i → Q.HasTripleIn A (Q.support i) → Q.s i < 5) (s : Sex)
    {X S : Finset (Fin n)} (hX : X ⊆ Q.XA A) (hS : S ⊆ Q.ZA A) :
    ∑ x ∈ X, Q.Ex h s x + ∑ z ∈ S, Q.Tz h s z ≤ Q.RA h s A := by
  unfold Member.RA
  have e := Finset.sum_le_sum_of_subset_of_nonneg hX
    (fun x hx _ => Ex_nonneg Q h hh (A := A) hx s)
  have t := Finset.sum_le_sum_of_subset_of_nonneg hS
    (fun z hz _ => Tz_nonneg' Q h hh hAI hP0 s hz)
  linarith

theorem parent_uv {s : Sex} {A B : Fin Q.R} {x p q u v : Fin n} (hAS : AS Q s A x p q B)
    (hp : Q.participants A = {u, v}) (hu : Q.IsFirst u A) (hv : Q.IsFirst v A) :
    p = u ∨ p = v := by
  have : p ∈ Q.firstGroup A := (mem_fg Q).mpr hAS.fp
  rw [fg_eq Q hp hu hv] at this
  simpa using this

theorem XA_card {A : Fin Q.R} {u v : Fin n} (hp : Q.participants A = {u, v})
    (hu : Q.IsFirst u A) (hv : Q.IsFirst v A) : (Q.XA A).card ≤ 2 := by
  by_contra hc
  push Not at hc
  obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ := Finset.two_lt_card.mp hc
  obtain ⟨pa, qa, Ba, ha'⟩ := as_XA Q ha .man
  obtain ⟨pb, qb, Bb, hb'⟩ := as_XA Q hb .man
  obtain ⟨pc, qc, Bc, hc''⟩ := as_XA Q hc' .man
  have key : ∀ {x y px qx py qy : Fin n} {Bx By : Fin Q.R}, AS Q .man A x px qx Bx →
      AS Q .man A y py qy By → px = py → x = y := by
    intro x y px qx py qy Bx By h1 h2 e
    rw [e] at h1; exact (h1.unique h2).1
  rcases parent_uv Q ha' hp hu hv with e1 | e1 <;> rcases parent_uv Q hb' hp hu hv with e2 | e2 <;>
    rcases parent_uv Q hc'' hp hu hv with e3 | e3
  all_goals first
    | exact hab (key ha' hb' (e1.trans e2.symm))
    | exact hac (key ha' hc'' (e1.trans e3.symm))
    | exact hbc (key hb' hc'' (e2.trans e3.symm))

end main

section cases
variable (Q : Member n) (h : ℕ → ℝ)

end cases

section perx
variable (Q : Member n) (h : ℕ → ℝ)

end perx

section final83
variable (Q : Member n) (h : ℕ → ℝ)

end final83

end Dev.L83

end StableCount
end

section
/-! The occurrence ledger (Table 1 and (14)) and Lemma 5.7: proofs of the interface `LedgerI.lean`. -/

namespace StableCount

namespace Dev.LG

variable {n : ℕ}

/-- The unreserved part of person `v`'s occurrence terms in sex `s`. -/
noncomputable def L (Q : Member n) (h : ℕ → ℝ) (s : Sex) (v : Fin n) : ℝ :=
  ∑ i ∈ Q.chainOf s (Q.person s v), Q.omegaTerm h s v i - (Q.beta h s v - Hsum h (Q.dL s v))

section helpers
open Dev.L52 Dev.L62 Dev.L83

variable (Q : Member n)

theorem rank_pos {s : Sex} {v : Fin n} {i : Fin Q.R} (hi : mv Q s i v) :
    1 ≤ Q.rank s (Q.person s v) i := by
  rw [rank_eq]
  exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩

theorem omega_at {h : ℕ → ℝ} {s : Sex} {v : Fin n} {i : Fin Q.R} {r : ℕ}
    (e : Q.rank s (Q.person s v) i = r) :
    Q.omegaTerm h s v i = ((Q.s i : ℝ) - r - 1) * h r := by
  unfold Member.omegaTerm; rw [e]

theorem omega_nonneg {h : ℕ → ℝ} (hh : IsAdmissible h) {s : Sex} {v : Fin n} {i : Fin Q.R}
    (hi : mv Q s i v) : 0 ≤ Q.omegaTerm h s v i := by
  unfold Member.omegaTerm
  have h1 := l51 Q s hi
  have h2 := hpos hh (rank_pos Q hi)
  have : ((Q.rank s (Q.person s v) i : ℕ) : ℝ) + 1 ≤ (Q.s i : ℝ) := by exact_mod_cast h1
  exact mul_nonneg (by linarith) h2.le

theorem rank1_eq {s : Sex} {v : Fin n} {i i0 : Fin Q.R} (h0 : Q.IsFirst v i0) (hi : mv Q s i v)
    (h1 : Q.rank s (Q.person s v) i = 1) : i = i0 := by
  have hr0 := rank_first Q s h0
  have hle : i0 ≤ i := not_lt.mp fun hl => (isFirst_mv Q s h0).2 i hl hi
  rcases hle.lt_or_eq with hl | he
  · have := Dev.L83.rank_mono Q s hi hl; omega
  · exact he.symm

theorem s_first_le {s : Sex} {v : Fin n} {i i0 : Fin Q.R} (h0 : Q.IsFirst v i0) (hi : mv Q s i v) :
    Q.s i0 ≤ Q.s i := by
  have hle : i0 ≤ i := not_lt.mp fun hl => (isFirst_mv Q s h0).2 i hl hi
  exact Finset.card_le_card
    (support_mono Q ((chain_le_iff Q s (isFirst_mv Q s h0).1 hi).mpr hle))

theorem dL_pos {s : Sex} {v : Fin n} (hv : v ∈ Q.V) : 1 ≤ Q.dL s v := by
  have h1 := first_rank Q s v hv
  have h2 := rank_le_dL Q s v (Q.first v hv)
  omega

theorem fg_sub (i : Fin Q.R) : Q.firstGroup i ⊆ Q.support i := by
  intro w hw
  simp only [Member.support, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨i, (mem_fg Q).mp hw, le_rfl' Q i⟩

/-- the counting identity: the rank-one and rank-two reservations -/
theorem sum_c (s : Sex) (v : Fin n) (hv : v ∈ Q.V) (a1 a2 : ℝ) :
    ∑ i ∈ Q.chainOf s (Q.person s v),
      ((if Q.rank s (Q.person s v) i = 1 then a1 else 0) +
        (if Q.rank s (Q.person s v) i = 2 then a2 else 0)) =
      a1 + (if 2 ≤ Q.dL s v then a2 else 0) := by
  have key := rank_sum (fun r => (if r = 1 then a1 else 0) + (if r = 2 then a2 else 0))
    (Q.chainOf s (Q.person s v))
  have hd := dL_pos Q (s := s) hv
  unfold Member.dL Member.deg at hd
  have e2 : ∑ r ∈ Finset.Icc 1 (Q.chainOf s (Q.person s v)).card,
      ((if r = 1 then a1 else 0) + (if r = 2 then a2 else 0)) =
      a1 + (if 2 ≤ (Q.chainOf s (Q.person s v)).card then a2 else 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
      if_pos (Finset.mem_Icc.mpr ⟨le_refl 1, hd⟩)]
    congr 1
    by_cases h2 : 2 ≤ (Q.chainOf s (Q.person s v)).card
    · rw [if_pos (Finset.mem_Icc.mpr ⟨by norm_num, h2⟩), if_pos h2]
    · rw [if_neg (fun h => h2 (Finset.mem_Icc.mp h).2), if_neg h2]
  unfold Member.rank
  exact key.trans e2

theorem L_ge {h : ℕ → ℝ} (s : Sex) (v : Fin n) (hv : v ∈ Q.V) (a1 a2 : ℝ) (g : Fin Q.R → ℝ)
    (hb : Q.beta h s v - Hsum h (Q.dL s v) ≤ a1 + (if 2 ≤ Q.dL s v then a2 else 0))
    (hg : ∀ i, mv Q s i v → g i + ((if Q.rank s (Q.person s v) i = 1 then a1 else 0) +
        (if Q.rank s (Q.person s v) i = 2 then a2 else 0)) ≤ Q.omegaTerm h s v i) :
    ∑ i ∈ Q.chainOf s (Q.person s v), g i ≤ L Q h s v := by
  unfold L
  have := Finset.sum_le_sum fun i hi => hg i ((mem_chainOf Q s _ i).mp hi)
  rw [Finset.sum_add_distrib, sum_c Q s v hv] at this
  linarith

theorem elem {h : ℕ → ℝ} {s : Sex} {v : Fin n} {i : Fin Q.R} (hi : mv Q s i v) (g a1 a2 : ℝ)
    (h1 : Q.rank s (Q.person s v) i = 1 → g + a1 ≤ Q.omegaTerm h s v i)
    (h2 : Q.rank s (Q.person s v) i = 2 → g + a2 ≤ Q.omegaTerm h s v i)
    (h3 : 3 ≤ Q.rank s (Q.person s v) i → g ≤ Q.omegaTerm h s v i) :
    g + ((if Q.rank s (Q.person s v) i = 1 then a1 else 0) +
      (if Q.rank s (Q.person s v) i = 2 then a2 else 0)) ≤ Q.omegaTerm h s v i := by
  have := rank_pos Q hi
  rcases (show Q.rank s (Q.person s v) i = 1 ∨ Q.rank s (Q.person s v) i = 2 ∨
      3 ≤ Q.rank s (Q.person s v) i by omega) with e | e | e
  · rw [if_pos e, if_neg (by omega)]; simpa using h1 e
  · rw [if_neg (by omega), if_pos e]; simpa using h2 e
  · rw [if_neg (by omega), if_neg (by omega)]; simpa using h3 e

/-! ### `β` by cases -/

theorem beta_ord {h : ℕ → ℝ} (s : Sex) {v : Fin n} {i : Fin Q.R} (hv : Q.IsFirst v i)
    (hi : Q.IsOrdinary i) :
    Q.beta h s v = if 3 ≤ (Q.firstGroup i).card then Hsum h (Q.dL s v) + h 1
      else Hsum h (Q.dL s v) + 2 * h 1 + (if 2 ≤ Q.dL s v then h 2 else 0) := by
  have c1 : ∃ i, Q.IsFirst v i ∧ Q.IsOrdinary i := ⟨i, hv, hi⟩
  have c2 : (∃ j, Q.IsFirst v j ∧ 3 ≤ (Q.firstGroup j).card) ↔ 3 ≤ (Q.firstGroup i).card := by
    constructor
    · rintro ⟨j, hj, h3⟩; rwa [isFirst_unique Q hj hv] at h3
    · intro h3; exact ⟨i, hv, h3⟩
  simp only [Member.beta]
  rw [if_pos c1]
  by_cases h3 : 3 ≤ (Q.firstGroup i).card
  · rw [if_pos (c2.mpr h3), if_pos h3]
  · rw [if_neg (fun h => h3 (c2.mp h)), if_neg h3]

theorem beta_exc {h : ℕ → ℝ} (s : Sex) {v : Fin n} (hx : Q.IsExceptional v) :
    Q.beta h s v = Hsum h (Q.dL s v) + h 1 + (if 2 ≤ Q.dL s v then h 2 else 0) := by
  have c1 : ¬ ∃ i, Q.IsFirst v i ∧ Q.IsOrdinary i := by
    rintro ⟨i, hi, hord⟩
    obtain ⟨j, hj, he⟩ := hx
    rw [isFirst_unique Q hj hi] at he
    exact hord.2.2 he
  simp only [Member.beta]
  rw [if_neg c1, if_pos hx]

open Classical in
theorem beta_rest {h : ℕ → ℝ} (s : Sex) {v : Fin n} (c1 : ¬ ∃ i, Q.IsFirst v i ∧ Q.IsOrdinary i)
    (hx : ¬ Q.IsExceptional v) :
    Q.beta h s v = if ∃ x, Q.IsParent s x v then Hsum h (Q.dL s v)
      else Hsum h (Q.dL s v) + (if 2 ≤ Q.dL s v then h 2 else 0) := by
  simp only [Member.beta]
  rw [if_neg c1, if_neg hx]

/-! ### Support bounds (Lemma 5.5) -/

/-- Lemma 5.5 (iii): an ordinary rotation with first group of size at most two has support at
least four. -/
theorem ord_small {G : Fin Q.R} (hG : Q.IsOrdinary G) (hk : (Q.firstGroup G).card ≤ 2) :
    4 ≤ Q.s G := by
  classical
  have hk1 : 1 ≤ (Q.firstGroup G).card := Finset.card_pos.mpr hG.1
  by_cases hall : ∀ m, mv Q .man G m → Q.IsFirst m G
  · exfalso
    have sub : Q.participants G ⊆ Q.firstGroup G := by
      intro w hw
      exact (mem_fg Q).mpr (hall w ((mem_participants Q G w).mp hw))
    have h2 := two_le_participants Q G
    have h3 := Finset.card_le_card sub
    have hc : (Q.participants G).card = 2 := by omega
    exact hG.2.1 ⟨hc, fun w hw => (mem_fg Q).mp (sub hw)⟩
  · push Not at hall
    obtain ⟨m, hm, hmG⟩ := hall
    obtain ⟨f, hf, hfG⟩ := exists_first Q .man hm
    have hfG' : f < G := lt_of_le_of_ne hfG fun e => hmG (e ▸ hf)
    have fleG : Q.le f G := chain_le Q .man (isFirst_mv Q .man hf).1 hm hfG'
    obtain ⟨a, b, hab, ha, hb⟩ := exists_two_mv Q .man f
    have nfa : a ∉ Q.firstGroup G := fun hh =>
      (isFirst_mv Q .man ((mem_fg Q).mp hh)).2 f hfG' ha
    have nfb : b ∉ Q.firstGroup G := fun hh =>
      (isFirst_mv Q .man ((mem_fg Q).mp hh)).2 f hfG' hb
    have sub : Q.firstGroup G ∪ {a, b} ⊆ Q.support G := by
      intro w hw
      rcases Finset.mem_union.mp hw with hw | hw
      · exact fg_sub Q G hw
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact support_mono Q fleG (mem_support_self Q .man ha)
        · exact support_mono Q fleG (mem_support_self Q .man hb)
    have disj : Disjoint (Q.firstGroup G) {a, b} := by
      rw [Finset.disjoint_left]
      intro w hw hw'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw'
      rcases hw' with rfl | rfl
      · exact nfa hw
      · exact nfb hw
    have hc := Finset.card_le_card sub
    rw [Finset.card_union_of_disjoint disj, Finset.card_pair hab] at hc
    unfold Member.s
    rcases (show (Q.firstGroup G).card = 1 ∨ (Q.firstGroup G).card = 2 by omega) with e | e
    · by_contra hlt
      exact hG.2.2 ⟨e, by unfold Member.s; omega⟩
    · omega

/-- Lemma 5.5 (ii), in the description of sex `s`: a participant of an initial swap that is not a
parent in sex `s` has a second support of size at least four. -/
theorem L55ii {s : Sex} {v : Fin n} {A : Fin Q.R} (hvA : Q.IsFirst v A) (hI : Q.IsInitialSwap A)
    (hnp : ¬ ∃ x, Q.IsParent s x v) {C : Fin Q.R} (hC : mv Q s C v)
    (hr : Q.rank s (Q.person s v) C = 2) : 4 ≤ Q.s C := by
  classical
  have hr0 := rank_first Q s hvA
  obtain ⟨hAC, -⟩ := next_of_rank Q s (isFirst_mv Q s hvA).1 hC (by rw [hr, hr0])
  have hleAC : Q.le A C := chain_le Q s (isFirst_mv Q s hvA).1 hC hAC
  have h3 : 3 ≤ Q.s C := by have := l51 Q s hC; omega
  by_contra hlt
  have hs3 : (Q.support C).card = 3 := by unfold Member.s at h3 hlt; omega
  have hfgA2 : (Q.firstGroup A).card = 2 := by
    have e : Q.firstGroup A = Q.participants A := by
      ext w
      rw [mem_fg]
      constructor
      · intro hw; exact (mem_participants Q A w).mpr (isFirst_mv Q .man hw).1
      · intro hw; exact hI.2 w hw
    rw [e, hI.1]
  have hsubA : Q.firstGroup A ⊆ Q.support C := (fg_sub Q A).trans (support_mono Q hleAC)
  obtain ⟨x, hxC, hxA⟩ : ∃ x ∈ Q.support C, x ∉ Q.firstGroup A := by
    by_contra hc
    push Not at hc
    have := Finset.card_le_card (show Q.support C ⊆ Q.firstGroup A from hc)
    omega
  have hSC : Q.support C = insert x (Q.firstGroup A) := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.insert_subset hxC hsubA)
    rw [Finset.card_insert_of_notMem hxA, hfgA2]; omega
  have memC : ∀ w ∈ Q.support C, w = x ∨ Q.IsFirst w A := by
    intro w hw
    rw [hSC, Finset.mem_insert] at hw
    rcases hw with e | e
    · exact Or.inl e
    · exact Or.inr ((mem_fg Q).mp e)
  obtain ⟨γ, hxγ, hγC⟩ : ∃ γ, Q.IsFirst x γ ∧ Q.le γ C := by
    have := hxC
    simp only [Member.support, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  have hγA : γ ≠ A := fun e => hxA ((mem_fg Q).mpr (e ▸ hxγ))
  have hfgγ : Q.firstGroup γ = {x} := by
    ext w
    rw [mem_fg, Finset.mem_singleton]
    constructor
    · intro hw
      have hwC : w ∈ Q.support C := support_mono Q hγC (fg_sub Q γ ((mem_fg Q).mpr hw))
      rcases memC w hwC with e | e
      · exact e
      · exact absurd (isFirst_unique Q hw e) hγA
    · rintro rfl; exact hxγ
  have hvx : v ≠ x := fun e => hxA ((mem_fg Q).mpr (e ▸ hvA))
  rcases eq_or_ne γ C with hγC' | hγC'
  · apply hnp
    refine ⟨x, ⟨γ, hxγ, by rw [hfgγ]; simp, ?_⟩, hvx, γ, hxγ, ?_⟩
    · rw [hγC']; unfold Member.s; exact hs3
    · rw [hγC']; exact hC
  · have hγlt : γ < C := lt_of_le_of_ne (le_idx Q hγC) hγC'
    have hs3γ : Q.s γ = 3 := by
      have a := single_s3 Q hfgγ
      have b := Finset.card_le_card (support_mono Q hγC)
      unfold Member.s at a ⊢; omega
    have hexc : Q.IsExceptionalSwap γ := ⟨by rw [hfgγ]; simp, hs3γ⟩
    obtain ⟨A', y, z, hs⟩ := assoc_of_exc Q x γ hxγ hexc
    have hxX := XA_of_assoc Q hs
    obtain ⟨p, q, B, hAS⟩ := as_XA Q hxX s
    have hBγ : B = γ := isFirst_unique Q hAS.fx hxγ
    rw [hBγ] at hAS
    have hpC : p ∈ Q.support C := support_mono Q hγC hAS.pSB
    have hqC : q ∈ Q.support C := support_mono Q hγC hAS.qSB
    have hpA : Q.IsFirst p A := (memC p hpC).resolve_left hAS.px
    have hA' : A' = A := isFirst_unique Q hAS.fp hpA
    rw [hA'] at hAS
    have inK : ∀ w ∈ Q.support C, w = p ∨ w = q ∨ w = x := by
      intro w hw
      rcases memC w hw with e | e
      · exact Or.inr (Or.inr e)
      · have : w ∈ Q.firstGroup A := (mem_fg Q).mpr e
        rw [fgA Q hAS] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
    rcases (hAS.mA v).mp (isFirst_mv Q s hvA).1 with e | e
    · apply hnp
      exact ⟨x, ⟨γ, hxγ, hexc⟩, hvx, γ, hxγ, e ▸ hAS.mvB1⟩
    · have hqCm : mv Q s C q := e ▸ hC
      obtain ⟨σ, hσ⟩ := down_perm Q s (isDn_down Q C)
      have hD := isDn_down Q C
      have AD : A ∈ Q.down C := (mem_down_iff Q C A).mpr hleAC
      have BD : γ ∈ Q.down C := (mem_down_iff Q C γ).mpr hγC
      have CD : C ∈ Q.down C := (mem_down_iff Q C C).mpr (le_rfl' Q C)
      have q1 : σ q ≠ q := by
        have := dp_ne Q hσ hD AD hAS.mvA2 (Fin.zero_le _); rwa [pm_zero] at this
      have q2 : σ q ≠ p := by
        have := dp_ne Q hσ hD CD hqCm (t1 := A.succ) (lt_succ_le hAC); rwa [hAS.pA2] at this
      have sq : σ q = x := by
        rcases inK _ (dp_down_mem Q hσ hqC) with e | e | e
        · exact absurd e q2
        · exact absurd e q1
        · exact e
      have p1 : σ p ≠ p := by
        have := dp_ne Q hσ hD AD hAS.mvA1 (Fin.zero_le _); rwa [pm_zero] at this
      have p2 : σ p ≠ q := by
        have := dp_ne Q hσ hD BD hAS.mvB1 (t1 := A.succ) (lt_succ_le hAS.lt)
        rwa [hAS.pA1] at this
      have sp : σ p = x := by
        rcases inK _ (dp_down_mem Q hσ hpC) with e | e | e
        · exact absurd e p1
        · exact absurd e p2
        · exact e
      exact hAS.pq (σ.injective (sp.trans sq.symm))

end helpers

open Dev.L52 Dev.L62 Dev.L83 in
theorem U_eq (Q : Member n) (h : ℕ → ℝ) (s : Sex) :
    Q.U h s = ∑ v ∈ Q.V, L Q h s v := by
  unfold Member.U Member.Omega L
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

open Dev.L52 Dev.L62 Dev.L83 in
theorem L_nonneg {h : ℕ → ℝ} (hh : IsAdmissible h) (Q : Member n) (s : Sex) (v : Fin n)
    (hv : v ∈ Q.V) : 0 ≤ L Q h s v := by
  have h0 : Q.IsFirst v (Q.first v hv) := ⟨hv, rfl⟩
  set i0 := Q.first v hv
  have p1 := hpos hh (le_refl 1)
  have p2 := hpos hh (show 1 ≤ 2 by norm_num)
  have h21 := hanti hh (le_refl 1) (show 1 ≤ 2 by norm_num)
  -- generic use of `L_ge` with `g = 0`
  have main : ∀ a1 a2 : ℝ,
      Q.beta h s v - Hsum h (Q.dL s v) ≤ a1 + (if 2 ≤ Q.dL s v then a2 else 0) →
      (Q.rank s (Q.person s v) i0 = 1 → a1 ≤ ((Q.s i0 : ℝ) - 1 - 1) * h 1) →
      (∀ i, mv Q s i v → Q.rank s (Q.person s v) i = 2 → a2 ≤ ((Q.s i : ℝ) - 2 - 1) * h 2) →
      0 ≤ L Q h s v := by
    intro a1 a2 hb ha1 ha2
    have := L_ge Q s v hv a1 a2 (fun _ => (0 : ℝ)) hb fun i hi => by
      apply elem Q hi
      · intro e
        have := rank1_eq Q h0 hi e
        subst this
        rw [omega_at Q e, zero_add]; push_cast; exact ha1 e
      · intro e
        rw [omega_at Q e, zero_add]; push_cast; exact ha2 i hi e
      · intro _; exact omega_nonneg Q hh hi
    simpa using this
  have hr2 : ∀ i, mv Q s i v → Q.rank s (Q.person s v) i = 2 → 4 ≤ Q.s i →
      h 2 ≤ ((Q.s i : ℝ) - 2 - 1) * h 2 := by
    intro i _ _ h4
    have : (4 : ℝ) ≤ Q.s i := by exact_mod_cast h4
    nlinarith
  have z2 : ∀ i, mv Q s i v → Q.rank s (Q.person s v) i = 2 →
      (0 : ℝ) ≤ ((Q.s i : ℝ) - 2 - 1) * h 2 := by
    intro i hi e
    have := l51 Q s hi
    rw [e] at this
    have : (3 : ℝ) ≤ Q.s i := by exact_mod_cast this
    nlinarith
  by_cases ho : ∃ i, Q.IsFirst v i ∧ Q.IsOrdinary i
  · obtain ⟨G, hG, hord⟩ := ho
    have hGi : G = i0 := isFirst_unique Q hG h0
    rw [hGi] at hord
    have hb := beta_ord Q (h := h) s h0 hord
    by_cases hk : 3 ≤ (Q.firstGroup i0).card
    · rw [if_pos hk] at hb
      apply main (h 1) 0 (by rw [hb]; simp) (fun _ => ?_) z2
      have a := Finset.card_le_card (fg_sub Q i0)
      have : (3 : ℝ) ≤ Q.s i0 := by exact_mod_cast (show 3 ≤ Q.s i0 by unfold Member.s; omega)
      nlinarith
    · rw [if_neg hk] at hb
      have h4 := ord_small Q hord (by omega)
      apply main (2 * h 1) (h 2) (by rw [hb]; linarith) (fun _ => ?_) (fun i hi e => ?_)
      · have : (4 : ℝ) ≤ Q.s i0 := by exact_mod_cast h4
        nlinarith
      · exact hr2 i hi e (h4.trans (s_first_le Q h0 hi))
  · by_cases hx : Q.IsExceptional v
    · have hb := beta_exc Q (h := h) s hx
      obtain ⟨B, hB, hexc⟩ := hx
      have hBi : B = i0 := isFirst_unique Q hB h0
      rw [hBi] at hexc
      apply main (h 1) (h 2) (by rw [hb]; linarith) (fun _ => ?_) (fun i hi e => ?_)
      · have : (Q.s i0 : ℝ) = 3 := by exact_mod_cast hexc.2
        rw [this]; linarith
      · obtain ⟨A, y, z, hs⟩ := assoc_of_exc Q v i0 h0 hexc
        obtain ⟨p, q, B', hAS⟩ := as_XA Q (XA_of_assoc Q hs) s
        have hB' : B' = i0 := isFirst_unique Q hAS.fx h0
        rw [hB'] at hAS
        obtain ⟨hlt, -⟩ := next_of_rank Q s hAS.mvB2 hi (by rw [e, rank_first Q s h0])
        exact hr2 i hi e (P1 Q hAS hi hlt)
    · have hb := beta_rest Q (h := h) s ho hx
      by_cases hp : ∃ x, Q.IsParent s x v
      · rw [if_pos hp] at hb
        apply main 0 0 (by rw [hb]; simp) (fun _ => ?_) z2
        have := l51 Q s (isFirst_mv Q s h0).1
        rw [rank_first Q s h0] at this
        have : (2 : ℝ) ≤ Q.s i0 := by exact_mod_cast this
        nlinarith
      · rw [if_neg hp] at hb
        have hI : Q.IsInitialSwap i0 := by
          by_contra hI
          apply ho
          refine ⟨i0, h0, ⟨v, (mem_fg Q).mpr h0⟩, hI, fun he => hx ⟨i0, h0, he⟩⟩
        apply main 0 (h 2) (by rw [hb]; simp) (fun _ => ?_) (fun i hi e => ?_)
        · have := l51 Q s (isFirst_mv Q s h0).1
          rw [rank_first Q s h0] at this
          have : (2 : ℝ) ≤ Q.s i0 := by exact_mod_cast this
          nlinarith
        · exact hr2 i hi e (L55ii Q h0 hI hp hi e)

open Dev.L52 Dev.L62 Dev.L83 in
theorem L_exc {h : ℕ → ℝ} (hh : IsAdmissible h) (Q : Member n) (s : Sex) (x : Fin n)
    (hx : Q.IsExceptional x) : Q.Ex h s x ≤ L Q h s x := by
  obtain ⟨B, hB, hexc⟩ := hx
  have hv : x ∈ Q.V := hB.1
  have p1 := hpos hh (le_refl 1)
  unfold Member.Ex
  rw [Finset.sum_filter]
  apply L_ge Q s x hv (h 1) (h 2)
  · rw [beta_exc Q s ⟨B, hB, hexc⟩]; linarith
  · intro i hi
    apply elem Q hi
    · intro e
      rw [if_neg (by omega), zero_add, omega_at Q e]
      have := rank1_eq Q hB hi e
      subst this
      have : (Q.s i : ℝ) = 3 := by exact_mod_cast hexc.2
      push_cast; rw [this]; linarith
    · intro e
      rw [if_pos (by omega), omega_at Q e, e]
      push_cast; linarith
    · intro e
      by_cases e3 : Q.rank s (Q.person s x) i = 3
      · rw [if_pos (by omega), omega_at Q e3, e3]
        push_cast; linarith
      · rw [if_neg (by omega)]
        exact omega_nonneg Q hh hi

open Dev.L52 Dev.L62 Dev.L83 in
theorem L_z {h : ℕ → ℝ} (hh : IsAdmissible h) (Q : Member n) (s : Sex) (z : Fin n) (i : Fin Q.R)
    (hz : Q.IsFirst z i) (hi : Q.IsOrdinary i) (hs : Q.s i = 4) (hk : (Q.firstGroup i).card = 1) :
    Q.Tz h s z - Q.atFirst (Q.Delta h s) z ≤ L Q h s z := by
  have hv : z ∈ Q.V := hz.1
  unfold Member.Tz
  rw [add_sub_cancel_left, Finset.sum_filter]
  apply L_ge Q s z hv (2 * h 1) (h 2)
  · rw [beta_ord Q s hz hi, if_neg (by omega)]; linarith
  · intro j hj
    apply elem Q hj
    · intro e
      rw [if_neg (by omega), zero_add, omega_at Q e]
      have := rank1_eq Q hz hj e
      subst this
      rw [hs]; push_cast; linarith
    · intro e
      rw [if_pos e, omega_at Q e]
      push_cast; linarith
    · intro e
      rw [if_neg (by omega)]
      exact omega_nonneg Q hh hj

open Dev.L52 Dev.L62 Dev.L83 in
theorem L_big {h : ℕ → ℝ} (hh : IsAdmissible h) (Q : Member n) (s : Sex) (v : Fin n) (i : Fin Q.R)
    (hv : Q.IsFirst v i) (hi : Q.IsOrdinary i) (hs : 5 ≤ Q.s i) :
    ((Q.s i : ℝ) - 4) * h 1 ≤ L Q h s v := by
  have hV : v ∈ Q.V := hv.1
  have p1 := hpos hh (le_refl 1)
  have p2 := hpos hh (show 1 ≤ 2 by norm_num)
  have hsum : ∑ j ∈ Q.chainOf s (Q.person s v),
      (if Q.rank s (Q.person s v) j = 1 then ((Q.s j : ℝ) - 4) * h 1 else 0) =
      ((Q.s i : ℝ) - 4) * h 1 := by
    rw [Finset.sum_eq_single i]
    · rw [if_pos (rank_first Q s hv)]
    · intro j hj hji
      rw [if_neg]
      exact fun e => hji (rank1_eq Q hv ((mem_chainOf Q s _ j).mp hj) e)
    · intro hn
      exact absurd ((mem_chainOf Q s _ i).mpr (isFirst_mv Q s hv).1) hn
  rw [← hsum]
  apply L_ge Q s v hV (2 * h 1) (h 2)
  · rw [beta_ord Q s hv hi]
    have : 0 ≤ (if 2 ≤ Q.dL s v then h 2 else 0) := by split_ifs <;> linarith
    split_ifs <;> linarith
  · intro j hj
    apply elem Q hj
    · intro e
      rw [if_pos e, omega_at Q e]
      push_cast; linarith
    · intro e
      rw [if_neg (by omega), zero_add, omega_at Q e]
      have h5 := hs.trans (s_first_le Q hv hj)
      have : (5 : ℝ) ≤ Q.s j := by exact_mod_cast h5
      push_cast; nlinarith
    · intro e
      rw [if_neg (by omega)]
      exact omega_nonneg Q hh hj

open Dev.L52 Dev.L62 Dev.L83 in
theorem delta_nonneg {h : ℕ → ℝ} (hh : IsAdmissible h) (Q : Member n) (s : Sex) (i : Fin Q.R)
    (hi : Q.IsOrdinary i) : 0 ≤ Q.Delta h s i := by
  unfold Member.Delta
  have hnn : ∀ r, 1 ≤ r → 0 ≤ h r := fun r hr => (hpos hh hr).le
  have hk : 0 < (Q.firstGroup i).card := Finset.card_pos.mpr hi.1
  have hkR : (0 : ℝ) < ((Q.firstGroup i).card : ℝ) := by exact_mod_cast hk
  have hdpos : ∀ v ∈ Q.firstGroup i, 1 ≤ Q.dL s v := fun v hv =>
    (tm_one Q h s i v (down_chain_single Q ((mem_fg Q).mp hv))).2
  -- (12)
  have hp : ∑ v ∈ Q.firstGroup i, h (Q.dL s v) ≤ Q.pLoss h s i := by
    rw [pLoss_eq]
    calc ∑ v ∈ Q.firstGroup i, h (Q.dL s v) = ∑ v ∈ Q.firstGroup i, tm Q h s i v :=
          Finset.sum_congr rfl fun v hv =>
            (tm_one Q h s i v (down_chain_single Q ((mem_fg Q).mp hv))).1.symm
      _ ≤ ∑ v, tm Q h s i v :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun v _ _ => tm_nonneg Q h hnn s i v)
  have hPpos : 0 < ∑ v ∈ Q.firstGroup i, h (Q.dL s v) :=
    Finset.sum_pos (fun v hv => hpos hh (hdpos v hv)) hi.1
  have l1 := lam_anti' hPpos hp
  -- (13), by Jensen
  have l2 : lam (∑ v ∈ Q.firstGroup i, h (Q.dL s v)) ≤
      ∑ v ∈ Q.firstGroup i, (1 / ((Q.firstGroup i).card : ℝ)) *
        lam (((Q.firstGroup i).card : ℝ) * h (Q.dL s v)) := by
    have J := lam_convex.map_sum_le (t := Q.firstGroup i)
      (w := fun _ => 1 / ((Q.firstGroup i).card : ℝ))
      (p := fun v => ((Q.firstGroup i).card : ℝ) * h (Q.dL s v))
      (fun _ _ => by positivity)
      (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
      (fun v hv => by
        simp only [Set.mem_Ioi]
        exact mul_pos hkR (hpos hh (hdpos v hv)))
    simp only [smul_eq_mul] at J
    have e : ∑ v ∈ Q.firstGroup i, 1 / ((Q.firstGroup i).card : ℝ) *
        (((Q.firstGroup i).card : ℝ) * h (Q.dL s v)) = ∑ v ∈ Q.firstGroup i, h (Q.dL s v) :=
      Finset.sum_congr rfl fun v _ => by field_simp
    rw [e] at J
    exact J
  -- per person
  have l3 : ∀ v ∈ Q.firstGroup i,
      lam (((Q.firstGroup i).card : ℝ) * h (Q.dL s v)) ≤ Q.beta h s v := by
    intro v hv
    have hvi : Q.IsFirst v i := (mem_fg Q).mp hv
    have hd := hdpos v hv
    have pd := hpos hh hd
    rw [beta_ord Q s hvi hi]
    by_cases h3 : 3 ≤ (Q.firstGroup i).card
    · rw [if_pos h3]
      have h3R : (3 : ℝ) ≤ ((Q.firstGroup i).card : ℝ) := by exact_mod_cast h3
      have a := lam_anti' (by positivity : 0 < 2 * h (Q.dL s v))
        (by nlinarith : 2 * h (Q.dL s v) ≤ ((Q.firstGroup i).card : ℝ) * h (Q.dL s v))
      have b := L56 hh hd
      have c : (if 2 ≤ Q.dL s v then h 2 else 0) ≤ h 1 := by
        split_ifs
        · exact hanti hh (le_refl 1) (by norm_num)
        · exact (hpos hh (le_refl 1)).le
      linarith
    · rw [if_neg h3]
      have h1R : (1 : ℝ) ≤ ((Q.firstGroup i).card : ℝ) := by exact_mod_cast hk
      exact Dev.L83.delta_nonneg hh hd (by nlinarith)
  have l4 : ∑ v ∈ Q.firstGroup i, lam (((Q.firstGroup i).card : ℝ) * h (Q.dL s v)) ≤
      ∑ v ∈ Q.firstGroup i, Q.beta h s v := Finset.sum_le_sum l3
  rw [← Finset.mul_sum] at l2
  have : ((Q.firstGroup i).card : ℝ) * lam (Q.pLoss h s i) ≤
      ∑ v ∈ Q.firstGroup i, lam (((Q.firstGroup i).card : ℝ) * h (Q.dL s v)) := by
    have := mul_le_mul_of_nonneg_left (l1.trans l2) hkR.le
    rwa [← mul_assoc, mul_one_div_cancel hkR.ne', one_mul] at this
  linarith

end Dev.LG

end StableCount
end

section
set_option autoImplicit false

namespace StableCount
open StableMatching
namespace Dev.P58
open Dev.L52 Dev.L62 Dev.L83

variable {n : ℕ}

section basic
variable (Q : Member n)

theorem fst_eq {v : Fin n} {i j : Fin Q.R} (hi : v ∈ Q.firstGroup i) (hj : v ∈ Q.firstGroup j) :
    i = j :=
  isFirst_unique Q ((mem_fg Q).mp hi) ((mem_fg Q).mp hj)

theorem fg_V {v : Fin n} {i : Fin Q.R} (hv : v ∈ Q.firstGroup i) : v ∈ Q.V :=
  ((mem_fg Q).mp hv).1

theorem fg_support {v : Fin n} {i : Fin Q.R} (hv : v ∈ Q.firstGroup i) : v ∈ Q.support i :=
  mem_support_self Q .man (isFirst_mv Q .man ((mem_fg Q).mp hv)).1

theorem init_not_exc {i : Fin Q.R} (hI : Q.IsInitialSwap i) : ¬ Q.IsExceptionalSwap i := by
  intro he
  have h1 := init_s2 Q hI
  have h2 := he.2
  omega

theorem XA_first {A : Fin Q.R} {x : Fin n} (hx : x ∈ Q.XA A) :
    ∃ B, x ∈ Q.firstGroup B ∧ Q.IsExceptionalSwap B := by
  simp only [Member.XA, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨⟨B, hB, he⟩, -⟩ := hx
  exact ⟨B, (mem_fg Q).mpr hB, he⟩

theorem XA_V {A : Fin Q.R} {x : Fin n} (hx : x ∈ Q.XA A) : x ∈ Q.V := by
  obtain ⟨B, hB, -⟩ := XA_first Q hx
  exact fg_V Q hB

theorem XA_unique {A A' : Fin Q.R} {x : Fin n} (h1 : x ∈ Q.XA A) (h2 : x ∈ Q.XA A') :
    A = A' := by
  obtain ⟨y, z, B, hs⟩ := assoc_of_XA Q A x h1
  obtain ⟨y', z', B', hs'⟩ := assoc_of_XA Q A' x h2
  have hB : B = B' := isFirst_unique Q hs.1 hs'.1
  subst hB
  have hd := hs.2.2.2.2.2.2.2.2.2.1
  have hd' := hs'.2.2.2.2.2.2.2.2.2.1
  have hm : A' ∈ Q.down B := by rw [hd']; simp
  rw [hd] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with e | e
  · exact e.symm
  · exact absurd e (ne_of_lt hs'.2.2.1)

/-- an exceptional label is not in the first group of an initial swap -/
theorem XA_not_fg {A A' : Fin Q.R} {x : Fin n} (hx : x ∈ Q.XA A) (hA' : Q.IsInitialSwap A') :
    x ∉ Q.firstGroup A' := by
  intro hm
  obtain ⟨B, hB, he⟩ := XA_first Q hx
  have := fst_eq Q hm hB
  subst this
  exact init_not_exc Q hA' he

theorem XA_not_ord {A i : Fin Q.R} {x : Fin n} (hx : x ∈ Q.XA A) (hi : Q.IsOrdinary i) :
    x ∉ Q.firstGroup i := by
  intro hm
  obtain ⟨B, hB, he⟩ := XA_first Q hx
  have := fst_eq Q hm hB
  subst this
  exact hi.2.2 he

theorem fg_init {A : Fin Q.R} (hA : Q.IsInitialSwap A) : Q.firstGroup A = Q.participants A := by
  ext v
  rw [mem_fg]
  constructor
  · intro hv
    exact (mem_participants Q A v).mpr (isFirst_mv Q .man hv).1
  · exact hA.2 v

theorem fg_init_card {A : Fin Q.R} (hA : Q.IsInitialSwap A) : (Q.firstGroup A).card = 2 := by
  rw [fg_init Q hA]; exact hA.1

theorem fg_disj {i j : Fin Q.R} (hij : i ≠ j) : Disjoint (Q.firstGroup i) (Q.firstGroup j) :=
  Finset.disjoint_left.mpr fun _ h1 h2 => hij (fst_eq Q h1 h2)

theorem triple_fg {A : Fin Q.R} {S : Finset (Fin n)} (ht : Q.HasTripleIn A S) :
    Q.firstGroup A ⊆ S := by
  obtain ⟨x, -, hsub⟩ := ht
  exact Finset.subset_union_left.trans hsub

end basic


section count
variable (Q : Member n)

/-- the labels of `A`'s triples inside `S` -/
noncomputable def tr (S : Finset (Fin n)) (A : Fin Q.R) : Finset (Fin n) :=
  (Q.firstGroup A ∪ Q.XA A) ∩ S

theorem tr_card {S : Finset (Fin n)} {A : Fin Q.R} (hA : Q.IsInitialSwap A)
    (ht : Q.HasTripleIn A S) : 3 ≤ (tr Q S A).card := by
  obtain ⟨x, hx, hsub⟩ := ht
  have hsub' : Q.firstGroup A ∪ {x} ⊆ tr Q S A := by
    intro w hw
    refine Finset.mem_inter.mpr ⟨?_, hsub hw⟩
    rcases Finset.mem_union.mp hw with h | h
    · exact Finset.mem_union_left _ h
    · rw [Finset.mem_singleton.mp h]; exact Finset.mem_union_right _ hx
  have hd : Disjoint (Q.firstGroup A) {x} :=
    Finset.disjoint_singleton_right.mpr (XA_not_fg Q hx hA)
  have := Finset.card_le_card hsub'
  rw [Finset.card_union_of_disjoint hd, fg_init_card Q hA, Finset.card_singleton] at this
  exact this

theorem tr_disj {S : Finset (Fin n)} {A A' : Fin Q.R} (hA : Q.IsInitialSwap A)
    (hA' : Q.IsInitialSwap A') (hne : A ≠ A') : Disjoint (tr Q S A) (tr Q S A') := by
  rw [Finset.disjoint_left]
  intro w h1 h2
  simp only [tr, Finset.mem_inter, Finset.mem_union] at h1 h2
  rcases h1.1 with a | a <;> rcases h2.1 with b | b
  · exact hne (fst_eq Q a b)
  · exact XA_not_fg Q b hA a
  · exact XA_not_fg Q a hA' b
  · exact hne (XA_unique Q a b)

theorem tr_fg {i : Fin Q.R} (hi : Q.IsOrdinary i) {S : Finset (Fin n)} {A : Fin Q.R}
    (hA : Q.IsInitialSwap A) : Disjoint (Q.firstGroup i) (tr Q S A) := by
  rw [Finset.disjoint_left]
  intro w h1 h2
  simp only [tr, Finset.mem_inter, Finset.mem_union] at h2
  rcases h2.1 with a | a
  · have := fst_eq Q h1 a
    subst this
    exact hi.2.1 hA
  · exact XA_not_ord Q a hi h1

/-- the counting of Lemma 8.1: `m ≤ k (s − 4)` -/
theorem count81 {i : Fin Q.R} (hi : Q.IsOrdinary i) (h5 : 5 ≤ Q.s i) (M : Finset (Fin Q.R))
    (hM : ∀ A ∈ M, Q.IsInitialSwap A ∧ Q.HasTripleIn A (Q.support i)) :
    M.card ≤ (Q.firstGroup i).card * (Q.s i - 4) := by
  classical
  set S := Q.support i
  have hpd : (M : Set (Fin Q.R)).PairwiseDisjoint (tr Q S) := by
    intro A hA A' hA' hne
    exact tr_disj Q (hM A hA).1 (hM A' hA').1 hne
  have hcardU : (M.biUnion (tr Q S)).card = ∑ A ∈ M, (tr Q S A).card :=
    Finset.card_biUnion hpd
  have h3 : 3 * M.card ≤ ∑ A ∈ M, (tr Q S A).card := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun A hA => tr_card Q (hM A hA).1 (hM A hA).2
  have hdisj : Disjoint (Q.firstGroup i) (M.biUnion (tr Q S)) := by
    rw [Finset.disjoint_biUnion_right]
    intro A hA
    exact tr_fg Q hi (hM A hA).1
  have hsub : Q.firstGroup i ∪ M.biUnion (tr Q S) ⊆ S := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · exact fg_support Q h
    · obtain ⟨A, -, hA⟩ := Finset.mem_biUnion.mp h
      exact (Finset.mem_inter.mp hA).2
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hcardU] at hle
  have hk : 1 ≤ (Q.firstGroup i).card := Finset.card_pos.mpr hi.1
  have hs : (Q.s i) = S.card := rfl
  set k := (Q.firstGroup i).card
  set m := M.card
  set s := Q.s i
  have key : 3 * m + k ≤ s := by omega
  rcases Nat.lt_or_ge m 2 with hm | hm
  · calc m ≤ 1 * 1 := by omega
      _ ≤ k * (s - 4) := Nat.mul_le_mul hk (by omega)
  · calc m ≤ 1 * (s - 4) := by omega
      _ ≤ k * (s - 4) := Nat.mul_le_mul_right _ hk

end count

section lemma81
variable (Q : Member n) {h : ℕ → ℝ}

theorem h21 (hh : IsAdmissible h) : 2 * h 2 ≤ h 1 := hh.2.2.2.2.2.1.1

theorem NA_le {A : Fin Q.R} (hA : Q.IsInitialSwap A) (s : Sex) : (Q.NA s A : ℝ) ≤ 2 := by
  obtain ⟨u, v, -, hp⟩ := Finset.card_eq_two.mp hA.1
  have hu : Q.IsFirst u A := hA.2 u (by rw [hp]; simp)
  have hv : Q.IsFirst v A := hA.2 v (by rw [hp]; simp)
  have h1 : Q.NA s A ≤ 2 := (Finset.card_filter_le _ _).trans (XA_card Q hp hu hv)
  exact_mod_cast h1

theorem DStar_le_h1 (hh : IsAdmissible h) {A : Fin Q.R} (hA : Q.IsInitialSwap A) :
    max (Q.DStar h A) 0 ≤ h 1 := by
  have hD := lemma_6_2 h hh Q A hA
  have hm := NA_le Q hA .man
  have hw := NA_le Q hA .woman
  have h2 : 0 < h 2 := hh.1 2 (by norm_num)
  have h1 : 0 < h 1 := hh.1 1 le_rfl
  have h21' := h21 hh
  apply max_le _ h1.le
  have : (h 2 / 2) * ((Q.NA .man A : ℝ) + (Q.NA .woman A : ℝ)) ≤ (h 2 / 2) * 4 :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

/-- Lemma 8.1, for any set `M` of initial swaps with a triple in `S(ρ)`, and one sex -/
theorem lemma81 (hh : IsAdmissible h) (s : Sex) {i : Fin Q.R} (hi : Q.IsOrdinary i)
    (h5 : 5 ≤ Q.s i) (M : Finset (Fin Q.R))
    (hM : ∀ A ∈ M, Q.IsInitialSwap A ∧ Q.HasTripleIn A (Q.support i)) :
    ∑ A ∈ M, max (Q.DStar h A) 0 ≤ ∑ v ∈ Q.firstGroup i, LG.L Q h s v := by
  have hc := count81 Q hi h5 M hM
  have h1 : 0 < h 1 := hh.1 1 le_rfl
  have e1 : ∑ A ∈ M, max (Q.DStar h A) 0 ≤ (M.card : ℝ) * h 1 := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun A hA => DStar_le_h1 Q hh (hM A hA).1
  have e2 : (M.card : ℝ) * h 1 ≤ ((Q.firstGroup i).card : ℝ) * (((Q.s i : ℝ) - 4) * h 1) := by
    have hc' : (M.card : ℝ) ≤ ((Q.firstGroup i).card : ℝ) * ((Q.s i : ℝ) - 4) := by
      have : ((Q.s i - 4 : ℕ) : ℝ) = (Q.s i : ℝ) - 4 := by
        rw [Nat.cast_sub (by omega)]; norm_num
      rw [← this]; exact_mod_cast hc
    nlinarith
  have e3 : ((Q.firstGroup i).card : ℝ) * (((Q.s i : ℝ) - 4) * h 1) ≤
      ∑ v ∈ Q.firstGroup i, LG.L Q h s v := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun v hv => LG.L_big hh Q s v i ((mem_fg Q).mp hv) hi h5
  linarith

end lemma81

section choice
variable (Q : Member n)

open Classical in
/-- the chosen rotation `ρ_A` for `A ∈ 𝒫₅` -/
noncomputable def ch (A : Fin Q.R) : Fin Q.R :=
  if hA : ∃ i, Q.IsOrdinary i ∧ 5 ≤ Q.s i ∧ Q.HasTripleIn A (Q.support i) then
    Classical.choose hA else A

theorem P5_spec {A : Fin Q.R} (hA : A ∈ Q.P5) :
    Q.IsInitialSwap A ∧ ∃ i, Q.IsOrdinary i ∧ 5 ≤ Q.s i ∧ Q.HasTripleIn A (Q.support i) := by
  simp only [Member.P5, Member.initialSwaps, Finset.mem_filter, Finset.mem_univ, true_and] at hA
  exact hA

theorem ch_spec {A : Fin Q.R} (hA : A ∈ Q.P5) :
    Q.IsOrdinary (ch Q A) ∧ 5 ≤ Q.s (ch Q A) ∧ Q.HasTripleIn A (Q.support (ch Q A)) := by
  have hex := (P5_spec Q hA).2
  unfold ch
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem C5_le {h : ℕ → ℝ} (hh : IsAdmissible h) (s : Sex) :
    ∑ A ∈ Q.P5, max (Q.DStar h A) 0 ≤
      ∑ i ∈ Q.P5.image (ch Q), ∑ v ∈ Q.firstGroup i, LG.L Q h s v := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := ch Q) (t := Q.P5.image (ch Q))
    (fun A hA => Finset.mem_image_of_mem _ hA)]
  apply Finset.sum_le_sum
  intro i hi
  obtain ⟨A0, hA0, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨ho, h5, -⟩ := ch_spec Q hA0
  apply lemma81 Q hh s ho h5
  intro A hA
  obtain ⟨hA1, hA2⟩ := Finset.mem_filter.mp hA
  refine ⟨(P5_spec Q hA1).1, ?_⟩
  rw [← hA2]
  exact (ch_spec Q hA1).2.2

end choice

section ledger
variable (Q : Member n)

theorem ZA_info {A : Fin Q.R} (hA : A ∈ Q.P0) {z : Fin n} (hz : z ∈ Q.ZA A) :
    ∃ G, z ∈ Q.firstGroup G ∧ Q.IsOrdinary G ∧ Q.firstGroup G = {z} ∧ Q.s G = 4 ∧
      Q.HasTripleIn A (Q.support G) := by
  obtain ⟨hAI, hP0⟩ := P0_spec Q hA
  obtain ⟨G, hzG, ho, fg, h4, ht⟩ := ZA_spec Q hAI hP0 hz
  have h5 := hP0 G ho ht
  exact ⟨G, (mem_fg Q).mpr hzG, ho, fg, by omega, ht⟩

theorem ZA_disj {A A' : Fin Q.R} (hA : A ∈ Q.P0) (hA' : A' ∈ Q.P0) (hne : A ≠ A') :
    Disjoint (Q.ZA A) (Q.ZA A') := by
  classical
  rw [Finset.disjoint_left]
  intro z h1 h2
  obtain ⟨G, hzG, ho, -, hs4, ht⟩ := ZA_info Q hA h1
  obtain ⟨G', hzG', -, -, -, ht'⟩ := ZA_info Q hA' h2
  have := fst_eq Q hzG hzG'
  subst this
  have hAI := (P0_spec Q hA).1
  have hAI' := (P0_spec Q hA').1
  have hzA : z ∉ Q.firstGroup A := fun hm => ho.2.1 (fst_eq Q hzG hm ▸ hAI)
  have hzA' : z ∉ Q.firstGroup A' := fun hm => ho.2.1 (fst_eq Q hzG hm ▸ hAI')
  have hsub : Q.firstGroup A ∪ Q.firstGroup A' ∪ {z} ⊆ Q.support G := by
    intro w hw
    simp only [Finset.mem_union, Finset.mem_singleton] at hw
    rcases hw with (h | h) | h
    · exact triple_fg Q ht h
    · exact triple_fg Q ht' h
    · rw [h]; exact fg_support Q hzG
  have hd1 : Disjoint (Q.firstGroup A ∪ Q.firstGroup A') {z} := by
    rw [Finset.disjoint_singleton_right, Finset.mem_union]
    rintro (h | h)
    · exact hzA h
    · exact hzA' h
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint (fg_disj Q hne),
    fg_init_card Q hAI, fg_init_card Q hAI', Finset.card_singleton] at hc
  have : (Q.support G).card = 4 := hs4
  omega

/-- the ledger: the label sets used are pairwise disjoint subsets of `V` -/
theorem ledger {h : ℕ → ℝ} (hh : IsAdmissible h) (s : Sex) :
    ∑ i ∈ Q.P5.image (ch Q), ∑ v ∈ Q.firstGroup i, LG.L Q h s v +
      ∑ A ∈ Q.P0, ∑ x ∈ Q.XA A, LG.L Q h s x + ∑ A ∈ Q.P0, ∑ z ∈ Q.ZA A, LG.L Q h s z ≤
      ∑ v ∈ Q.V, LG.L Q h s v := by
  classical
  set Rho := Q.P5.image (ch Q)
  have hRho : ∀ i ∈ Rho, Q.IsOrdinary i ∧ 5 ≤ Q.s i := by
    intro i hi
    obtain ⟨A0, hA0, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨(ch_spec Q hA0).1, (ch_spec Q hA0).2.1⟩
  have pd1 : (Rho : Set (Fin Q.R)).PairwiseDisjoint (Q.firstGroup) :=
    fun i _ j _ hne => fg_disj Q hne
  have pd2 : (Q.P0 : Set (Fin Q.R)).PairwiseDisjoint (Q.XA) := by
    intro A _ A' _ hne
    exact Finset.disjoint_left.mpr fun x h1 h2 => hne (XA_unique Q h1 h2)
  have pd3 : (Q.P0 : Set (Fin Q.R)).PairwiseDisjoint (Q.ZA) :=
    fun A hA A' hA' hne => ZA_disj Q hA hA' hne
  rw [← Finset.sum_biUnion pd1, ← Finset.sum_biUnion pd2, ← Finset.sum_biUnion pd3]
  set S1 := Rho.biUnion Q.firstGroup
  set S2 := Q.P0.biUnion Q.XA
  set S3 := Q.P0.biUnion Q.ZA
  have d12 : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    obtain ⟨i, hi, hv⟩ := Finset.mem_biUnion.mp h1
    obtain ⟨A, -, hx⟩ := Finset.mem_biUnion.mp h2
    exact XA_not_ord Q hx (hRho i hi).1 hv
  have d3 : Disjoint (S1 ∪ S2) S3 := by
    rw [Finset.disjoint_left]
    intro v h12 h3
    obtain ⟨A, hA, hz⟩ := Finset.mem_biUnion.mp h3
    obtain ⟨G, hzG, ho, -, hs4, -⟩ := ZA_info Q hA hz
    rcases Finset.mem_union.mp h12 with h1 | h2
    · obtain ⟨i, hi, hv⟩ := Finset.mem_biUnion.mp h1
      have := fst_eq Q hv hzG
      subst this
      have := (hRho i hi).2
      omega
    · obtain ⟨A', -, hx⟩ := Finset.mem_biUnion.mp h2
      exact XA_not_ord Q hx ho hzG
  rw [← Finset.sum_union d12, ← Finset.sum_union d3]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro v hv
    simp only [Finset.mem_union, S1, S2, S3, Finset.mem_biUnion] at hv
    rcases hv with ((⟨i, -, hv⟩ | ⟨A, -, hv⟩) | ⟨A, hA, hv⟩)
    · exact fg_V Q hv
    · exact XA_V Q hv
    · obtain ⟨G, hzG, -⟩ := ZA_info Q hA hv
      exact fg_V Q hzG
  · intro v hv _
    exact LG.L_nonneg hh Q s v hv

/-- the ordinary savings used by the `T_z` are distinct -/
theorem ZA_delta {h : ℕ → ℝ} (hh : IsAdmissible h) (s : Sex) :
    ∑ A ∈ Q.P0, ∑ z ∈ Q.ZA A, Q.atFirst (Q.Delta h s) z ≤ ∑ i ∈ Q.ordinary, Q.Delta h s i := by
  classical
  have pd3 : (Q.P0 : Set (Fin Q.R)).PairwiseDisjoint (Q.ZA) :=
    fun A hA A' hA' hne => ZA_disj Q hA hA' hne
  rw [← Finset.sum_biUnion pd3]
  set S3 := Q.P0.biUnion Q.ZA
  have hpt : ∀ z ∈ S3, Q.atFirst (Q.Delta h s) z =
      ∑ i ∈ Q.ordinary, if z ∈ Q.firstGroup i then Q.Delta h s i else 0 := by
    intro z hz
    obtain ⟨A, hA, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨G, hzG, ho, -⟩ := ZA_info Q hA hz
    rw [atFirst_eq Q ((mem_fg Q).mp hzG)]
    have : ∀ i ∈ Q.ordinary, (if z ∈ Q.firstGroup i then Q.Delta h s i else 0) =
        if G = i then Q.Delta h s i else 0 := by
      intro i _
      by_cases e : G = i
      · subst e; simp [hzG]
      · have : z ∉ Q.firstGroup i := fun hm => e (fst_eq Q hzG hm)
        simp [this, e]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    have hGo : G ∈ Q.ordinary := by simp [Member.ordinary, ho]
    simp [hGo]
  rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i hi
  have ho : Q.IsOrdinary i := by simpa [Member.ordinary] using hi
  have hD := LG.delta_nonneg hh Q s i ho
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : (S3.filter fun z => z ∈ Q.firstGroup i).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    obtain ⟨-, hb2⟩ := Finset.mem_filter.mp hb
    obtain ⟨A, hA, hz⟩ := Finset.mem_biUnion.mp ha1
    obtain ⟨G, hzG, -, fg, -⟩ := ZA_info Q hA hz
    have := fst_eq Q hzG ha2
    subst this
    rw [fg] at hb2
    exact (Finset.mem_singleton.mp hb2).symm
  have hc' : ((S3.filter fun z => z ∈ Q.firstGroup i).card : ℝ) ≤ 1 := by exact_mod_cast hc
  nlinarith

end ledger

section final
variable (Q : Member n)

theorem RA_le {h : ℕ → ℝ} (hh : IsAdmissible h) (s : Sex) {A : Fin Q.R} (hA : A ∈ Q.P0) :
    Q.RA h s A ≤ ∑ x ∈ Q.XA A, LG.L Q h s x + ∑ z ∈ Q.ZA A, LG.L Q h s z +
      ∑ z ∈ Q.ZA A, Q.atFirst (Q.Delta h s) z := by
  unfold Member.RA
  have e1 : ∑ x ∈ Q.XA A, Q.Ex h s x ≤ ∑ x ∈ Q.XA A, LG.L Q h s x :=
    Finset.sum_le_sum fun x hx => LG.L_exc hh Q s x (by
      simp only [Member.XA, Finset.mem_filter, Finset.mem_univ, true_and] at hx; exact hx.1)
  have e2 : ∑ z ∈ Q.ZA A, Q.Tz h s z ≤
      ∑ z ∈ Q.ZA A, (LG.L Q h s z + Q.atFirst (Q.Delta h s) z) := by
    apply Finset.sum_le_sum
    intro z hz
    obtain ⟨G, hzG, ho, fg, hs4, -⟩ := ZA_info Q hA hz
    have := LG.L_z hh Q s z G ((mem_fg Q).mp hzG) ho hs4 (by rw [fg]; simp)
    linarith
  rw [Finset.sum_add_distrib] at e2
  linarith

/-- display (25) -/
theorem eq25 {h : ℕ → ℝ} (hh : IsAdmissible h) (s : Sex) :
    ∑ A ∈ Q.P5, max (Q.DStar h A) 0 + ∑ A ∈ Q.P0, Q.RA h s A ≤
      Q.U h s + ∑ i ∈ Q.ordinary, Q.Delta h s i := by
  have c5 := C5_le Q hh s
  have hl := ledger Q hh s
  have hz := ZA_delta Q hh s
  have hr : ∑ A ∈ Q.P0, Q.RA h s A ≤
      ∑ A ∈ Q.P0, ∑ x ∈ Q.XA A, LG.L Q h s x + ∑ A ∈ Q.P0, ∑ z ∈ Q.ZA A, LG.L Q h s z +
        ∑ A ∈ Q.P0, ∑ z ∈ Q.ZA A, Q.atFirst (Q.Delta h s) z := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun A hA => RA_le Q hh s hA
  rw [LG.U_eq]
  linarith

theorem P0_bound {h : ℕ → ℝ} (hh : IsAdmissible h) {A : Fin Q.R} (hA : A ∈ Q.P0) :
    Q.DStar h A ≤ (Q.RA h .man A + Q.RA h .woman A) / 2 := by
  obtain ⟨hAI, hP0⟩ := P0_spec Q hA
  have r0 : ∀ s, 0 ≤ Q.RA h s A := fun s => by
    have := RA_ge Q h hh hAI hP0 s (X := ∅) (S := ∅) (Finset.empty_subset _)
      (Finset.empty_subset _)
    simpa using this
  by_cases hD : 0 < Q.DStar h A
  · have h6 := lemma_6_2 h hh Q A hAI
    have hm := lemma_8_3 h hh Q A hA hD .man
    have hw := lemma_8_3 h hh Q A hA hD .woman
    linarith
  · have := r0 .man
    have := r0 .woman
    linarith

end final

end Dev.P58

open Dev.P58 in
theorem chk_proposition_5_8 {n : ℕ} (h : ℕ → ℝ) (hh : IsAdmissible h) (Q : Member n) :
    ∑ A ∈ Q.initialSwaps, Q.DStar h A ≤
      (Q.U h .man + Q.U h .woman) / 2 +
        (1 / 2) * ∑ i ∈ Q.ordinary, (Q.Delta h .man i + Q.Delta h .woman i) := by
  have hsub : Q.P5 ⊆ Q.initialSwaps := fun A hA => by
    simp [Member.initialSwaps, (P5_spec Q hA).1]
  rw [← Finset.sum_sdiff hsub]
  have e5 : ∑ A ∈ Q.P5, Q.DStar h A ≤ ∑ A ∈ Q.P5, max (Q.DStar h A) 0 :=
    Finset.sum_le_sum fun A _ => le_max_left _ _
  have e0 : ∑ A ∈ Q.initialSwaps \ Q.P5, Q.DStar h A ≤
      ∑ A ∈ Q.P0, (Q.RA h .man A + Q.RA h .woman A) / 2 :=
    Finset.sum_le_sum fun A hA => P0_bound Q hh hA
  rw [← Finset.sum_div, Finset.sum_add_distrib] at e0
  have em := eq25 Q hh .man
  have ew := eq25 Q hh .woman
  rw [Finset.sum_add_distrib]
  linarith


end StableCount
end

theorem solution : type_of% @StableCount.chk_proposition_5_8 := @StableCount.chk_proposition_5_8
