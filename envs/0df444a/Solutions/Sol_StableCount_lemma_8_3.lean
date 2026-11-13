-- Prove2me | solution 1 for StableCount.lemma_8_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T00:09:57.227194+00:00
-- url     : https://prove2.me/submissions/5a92047a-b00e-411b-a717-90f9c81a26fe

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

/-- the function `z ↦ λ(T + z) − λ(2z)` is monotone on `(0, T]` -/
theorem mono23 {T z1 z2 : ℝ} (h1 : 0 < z1) (h12 : z1 ≤ z2) (h2T : z2 ≤ T) :
    lam (T + z1) - lam (2 * z1) ≤ lam (T + z2) - lam (2 * z2) := by
  rcases h12.lt_or_eq with hlt | heq
  · have m : ∀ x, 0 < x → x ∈ Set.Ioi (0 : ℝ) := fun x hx => hx
    have sa := lam_convex.secant_mono (a := 2 * z1) (x := 2 * z2) (y := T + z2) (m _ (by linarith))
      (m _ (by linarith)) (m _ (by linarith)) (by linarith) (by linarith) (by linarith)
    have sb := lam_convex.secant_mono (a := T + z2) (x := 2 * z1) (y := T + z1) (m _ (by linarith))
      (m _ (by linarith)) (m _ (by linarith)) (by linarith) (by linarith) (by linarith)
    have d1 : (0 : ℝ) < 2 * z2 - 2 * z1 := by linarith
    have d2 : (0 : ℝ) < T + z2 - 2 * z1 := by linarith
    have d3 : (2 * z1 - (T + z2)) = -(T + z2 - 2 * z1) := by ring
    have d4 : (T + z1 - (T + z2)) = -(z2 - z1) := by ring
    rw [d3, d4, div_neg, div_neg, neg_le_neg_iff] at sb
    have dec : lam (2 * z2) ≤ lam (2 * z1) := lam_anti' (by linarith) (by linarith)
    set S1 := (lam (2 * z2) - lam (2 * z1)) / (2 * z2 - 2 * z1) with hS1
    set S3 := (lam (T + z2) - lam (2 * z1)) / (T + z2 - 2 * z1) with hS3
    have hS3' : (lam (2 * z1) - lam (T + z2)) / (T + z2 - 2 * z1) = -S3 := by
      rw [hS3, ← neg_div]; congr 1; ring
    rw [hS3'] at sb
    set S2 := (lam (T + z1) - lam (T + z2)) / (z2 - z1) with hS2
    have e1 : S1 * (2 * z2 - 2 * z1) = lam (2 * z2) - lam (2 * z1) := div_mul_cancel₀ _ d1.ne'
    have e2 : S2 * (z2 - z1) = lam (T + z1) - lam (T + z2) := div_mul_cancel₀ _ (by linarith)
    have hS1n : S1 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) d1.le
    -- S1 ≤ S3 ≤ -S2
    have k : S1 ≤ -S2 := by linarith
    have : (2 * z2 - 2 * z1) * S1 ≤ (z2 - z1) * (-S2) := by nlinarith
    linarith
  · subst heq; exact le_refl _

theorem num1 {b : ℝ} (hb : 0 < b) (hb2 : b ≤ 4 / 25) : lam (5 * b) + 3 * b < lam (2 * b) := by
  unfold lam
  set y := Real.exp (-b) with hy
  have e2 : Real.exp (-(2 * b)) = y ^ 2 := by have := exp_pow' b 2; push_cast at this; exact this
  have e5 : Real.exp (-(5 * b)) = y ^ 5 := by have := exp_pow' b 5; push_cast at this; exact this
  have e3 : Real.exp (3 * b) * y ^ 3 = 1 := by
    rw [hy, ← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf; exact Real.exp_zero
  have hy1 : y < 1 := by rw [hy]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hy0 : 21 / 25 ≤ y := by have := Real.add_one_le_exp (-b); rw [hy]; linarith
  rw [e2, e5]
  have yp : 0 < y := by linarith
  have p2 : 0 < 1 - y ^ 2 := by nlinarith
  have p5 : 0 < 1 - y ^ 5 := by
    have : y ^ 5 < 1 := pow_lt_one₀ yp.le hy1 (by norm_num)
    linarith
  have q3 := pow_le_pow_left₀ (by norm_num) hy0 3
  have q4 := pow_le_pow_left₀ (by norm_num) hy0 4
  have q5 := pow_le_pow_left₀ (by norm_num) hy0 5
  have q6 := pow_le_pow_left₀ (by norm_num) hy0 6
  have q7 := pow_le_pow_left₀ (by norm_num) hy0 7
  have br : 0 < y ^ 3 + y ^ 4 + y ^ 5 + y ^ 6 + y ^ 7 - 1 - y := by
    norm_num at q3 q4 q5 q6 q7; linarith
  have poly : 1 - y ^ 2 < (1 - y ^ 5) * y ^ 3 := by
    have : (1 - y ^ 5) * y ^ 3 - (1 - y ^ 2) =
        (1 - y) * (y ^ 3 + y ^ 4 + y ^ 5 + y ^ 6 + y ^ 7 - 1 - y) := by ring
    have : 0 < (1 - y) * (y ^ 3 + y ^ 4 + y ^ 5 + y ^ 6 + y ^ 7 - 1 - y) :=
      mul_pos (by linarith) br
    linarith
  have E := Real.exp_pos (3 * b)
  have key : (1 - y ^ 2) * Real.exp (3 * b) < 1 - y ^ 5 := by
    have y3 : 0 < y ^ 3 := by positivity
    have : (1 - y ^ 2) * Real.exp (3 * b) * y ^ 3 < (1 - y ^ 5) * y ^ 3 := by
      calc (1 - y ^ 2) * Real.exp (3 * b) * y ^ 3 = (1 - y ^ 2) * (Real.exp (3 * b) * y ^ 3) := by ring
        _ = 1 - y ^ 2 := by rw [e3, mul_one]
        _ < _ := poly
    exact lt_of_mul_lt_mul_right this y3.le
  have := Real.log_lt_log (mul_pos p2 E) key
  rw [Real.log_mul p2.ne' E.ne', Real.log_exp] at this
  linarith

theorem exp_small : Real.exp (8 / 25) + Real.exp (-(13 / 25)) < 2 := by
  have a1 := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 25) (by norm_num) (by norm_num)
  have a8 : Real.exp (8 / 25) = Real.exp (1 / 25) ^ 8 := by
    rw [← Real.exp_nat_mul]; norm_num
  have a8' : Real.exp (1 / 25) ^ 8 < (1 / (1 - 1 / 25)) ^ 8 :=
    pow_lt_pow_left₀ a1 (Real.exp_pos _).le (by norm_num)
  have b1 := Real.quadratic_le_exp_of_nonneg (x := 13 / 50) (by norm_num)
  have b2 : Real.exp (13 / 25) = Real.exp (13 / 50) ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  have b2' : (1 + 13 / 50 + (13 / 50) ^ 2 / 2 : ℝ) ^ 2 ≤ Real.exp (13 / 50) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) b1 2
  have b3 : Real.exp (-(13 / 25)) * Real.exp (13 / 25) = 1 := by
    rw [← Real.exp_add]; norm_num
  have hp := Real.exp_pos (-(13 / 25))
  norm_num at a8' b2'
  rw [a8]
  nlinarith

theorem num2 {b c : ℝ} (hb : 0 < b) (hb2 : b ≤ 4 / 25) (hc : 5 * b / 8 ≤ c) :
    lam (2 * b + 2 * c) + 2 * b < lam (2 * b) := by
  unfold lam
  set θ := 25 * b / 4 with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  have c1 := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (8 / 25 : ℝ))
    (by linarith : 0 ≤ 1 - θ) hθ0 (by ring)
  have c2 := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-(13 / 25) : ℝ))
    (by linarith : 0 ≤ 1 - θ) hθ0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at c1 c2
  have e1 : θ * (8 / 25) = 2 * b := by rw [hθ]; ring
  have e2 : θ * (-(13 / 25)) = -(13 * b / 4) := by rw [hθ]; ring
  rw [e1] at c1
  rw [e2] at c2
  have m : Real.exp (-(2 * b + 2 * c)) ≤ Real.exp (-(13 * b / 4)) :=
    Real.exp_le_exp.mpr (by linarith)
  have es := exp_small
  have hθp : 0 < θ := by positivity
  have sum2 : Real.exp (2 * b) + Real.exp (-(2 * b + 2 * c)) < 2 := by nlinarith
  have p2 := ose_pos (by linarith : 0 < 2 * b)
  have p22 := ose_pos (by linarith : 0 < 2 * b + 2 * c)
  have E := Real.exp_pos (2 * b)
  have key : (1 - Real.exp (-(2 * b))) * Real.exp (2 * b) < 1 - Real.exp (-(2 * b + 2 * c)) := by
    have : Real.exp (-(2 * b)) * Real.exp (2 * b) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have := Real.log_lt_log (mul_pos p2 E) key
  rw [Real.log_mul p2.ne' E.ne', Real.log_exp] at this
  linarith

/-- Lemma 8.2 (ii), `d = 1`: `4a − λ(a + b) > 2b` -/
theorem num3 {a b : ℝ} (ha : Real.log 2 ≤ 2 * a) (hb : 0 < b) (hba : 2 * b ≤ a) :
    lam (a + b) < 4 * a - 2 * b := by
  have ha0 : 0 < a := by linarith
  set θ := b / a with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one ha0]; linarith
  have hθa : θ * a = b := by rw [hθ]; field_simp
  have c1 := convexOn_exp.2 (Set.mem_univ (-(4 * a))) (Set.mem_univ (-(2 * a)))
    (by linarith : 0 ≤ 1 - θ) hθ0 (by ring)
  have c2 := convexOn_exp.2 (Set.mem_univ (-a)) (Set.mem_univ (-(2 * a)))
    (by linarith : 0 ≤ 1 - θ) hθ0 (by ring)
  simp only [smul_eq_mul] at c1 c2
  have e1 : (1 - θ) * -(4 * a) + θ * -(2 * a) = -(4 * a - 2 * b) := by rw [← hθa]; ring
  have e2 : (1 - θ) * -a + θ * -(2 * a) = -(a + b) := by rw [← hθa]; ring
  rw [e1] at c1
  rw [e2] at c2
  set y := Real.exp (-a) with hy
  have y2 : Real.exp (-(2 * a)) = y ^ 2 := by have := exp_pow' a 2; push_cast at this; exact this
  have y4 : Real.exp (-(4 * a)) = y ^ 4 := by have := exp_pow' a 4; push_cast at this; exact this
  rw [y2] at c1 c2
  rw [y4] at c1
  have yp : 0 < y := Real.exp_pos _
  have hy2 : y ^ 2 ≤ 1 / 2 := by
    rw [← y2]
    have : Real.exp (-(2 * a)) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith)
    have e : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    linarith
  have hy34 : y < 3 / 4 := by nlinarith
  have hy4 : y ^ 4 ≤ 1 / 4 := by nlinarith
  have hθlt : θ < 1 := by rw [hθ, div_lt_one ha0]; linarith
  have sum1 : Real.exp (-(4 * a - 2 * b)) + Real.exp (-(a + b)) < 1 := by nlinarith
  unfold lam
  have p := ose_pos (by linarith : 0 < a + b)
  have : Real.exp (-(4 * a - 2 * b)) < 1 - Real.exp (-(a + b)) := by linarith
  have := (Real.lt_log_iff_exp_lt p).mpr this
  linarith

section adm
variable {h : ℕ → ℝ}

theorem lem23 (hh : IsAdmissible h) {j : ℕ} (hj : 2 ≤ j) {T : ℝ} (hT : h 2 ≤ T) :
    lam (T + h j) - Aval h j ≤ lam (T + h 2) - lam (2 * h 2) - h 1 - h 2 := by
  have pj := hpos hh (show 1 ≤ j by omega)
  have hj2 : h j ≤ h 2 := hanti hh (by norm_num) hj
  have m := mono23 pj hj2 hT
  have H2 := hh.2.2.2.1 j hj
  rw [Aval, if_neg (by omega)]
  linarith

theorem eta2hat (hh : IsAdmissible h) {j : ℕ} (hj : 2 ≤ j) :
    lam (h (2 - 1) + 2 * h 2 + h j) - Aval h j ≤ Hsum h 2 - lam (2 * h 2) - h 1 - 3 * h 2 := by
  have p2 := hpos hh (show 1 ≤ 2 by norm_num)
  obtain ⟨H41, H42, H43⟩ := hh.2.2.2.2.2.1
  obtain ⟨H51, H52⟩ := hh.2.2.2.2.2.2
  have H2 := hh.2.2.2.1 2 le_rfl
  rw [show (2 : ℕ) - 1 = 1 from rfl]
  have l := lem23 hh hj (T := h 1 + 2 * h 2) (by linarith)
  have b4 : h 2 ≤ 4 / 25 := by linarith
  have n1 := num1 p2 b4
  have an := lam_anti' (by positivity : 0 < 5 * h 2) (by linarith : 5 * h 2 ≤ h 1 + 2 * h 2 + h 2)
  linarith

theorem eta2 (hh : IsAdmissible h) {j : ℕ} (hj : 1 ≤ j) :
    lam (h (2 - 1) + 2 * h 2 + h j) - Aval h j ≤ Hsum h 2 - lam (2 * h 2) - h 1 - h 2 := by
  rcases (show j = 1 ∨ 2 ≤ j by omega) with rfl | hj2
  · have p1 := hpos hh (le_refl 1)
    have p2 := hpos hh (show 1 ≤ 2 by norm_num)
    obtain ⟨H41, H42, H43⟩ := hh.2.2.2.2.2.1
    have H2 := hh.2.2.2.1 2 le_rfl
    have s1 := L56 hh (le_refl 1)
    rw [if_neg (by norm_num), Hsum_one, add_zero] at s1
    rw [show (2 : ℕ) - 1 = 1 from rfl, Aval, if_pos rfl]
    have an := lam_anti' (by positivity : 0 < 2 * h 1) (by linarith : 2 * h 1 ≤ h 1 + 2 * h 2 + h 1)
    linarith
  · have := eta2hat hh hj2
    have p2 := hpos hh (show 1 ≤ 2 by norm_num)
    linarith

theorem eta3hat (hh : IsAdmissible h) {j : ℕ} (hj : 2 ≤ j) :
    lam (h (3 - 1) + 2 * h 3 + h j) - Aval h j ≤ Hsum h 3 - lam (2 * h 3) - 4 * h 2 := by
  have p2 := hpos hh (show 1 ≤ 2 by norm_num)
  have p3 := hpos hh (show 1 ≤ 3 by norm_num)
  obtain ⟨H41, H42, H43⟩ := hh.2.2.2.2.2.1
  obtain ⟨H51, H52⟩ := hh.2.2.2.2.2.2
  have H2 := hh.2.2.2.1 3 (by norm_num)
  rw [show (3 : ℕ) - 1 = 2 from rfl]
  have l := lem23 hh hj (T := h 2 + 2 * h 3) (by linarith)
  have b4 : h 2 ≤ 4 / 25 := by linarith
  have n2 := num2 p2 b4 (c := h 3) (by linarith)
  have e : h 2 + 2 * h 3 + h 2 = 2 * h 2 + 2 * h 3 := by ring
  rw [e] at l
  linarith

/-- the slack retained for a parent of degree `d` whose two exceptional labels have degrees
`c1, c2` (Lemma 7.1) -/
noncomputable def eta (h : ℕ → ℝ) (d c1 c2 : ℕ) : ℝ :=
  if d = 2 then (if 2 ≤ c1 ∧ 2 ≤ c2 then 3 * h 2 else h 2)
  else if d = 3 ∧ 2 ≤ c1 ∧ 2 ≤ c2 then 4 * h 2 else 0

theorem eta_ok (hh : IsAdmissible h) {d c1 c2 j : ℕ} (hd : 2 ≤ d) (hc1 : 1 ≤ c1) (hc2 : 1 ≤ c2)
    (hj : j = c1 ∨ j = c2) :
    lam (h (d - 1) + 2 * h d + h j) - Aval h j ≤
      Hsum h d - lam (2 * h d) - (if d = 2 then h 1 else 0) - eta h d c1 c2 := by
  have hj1 : 1 ≤ j := by rcases hj with rfl | rfl <;> assumption
  unfold eta
  rcases (show d = 2 ∨ d = 3 ∨ 4 ≤ d by omega) with rfl | rfl | hd4
  · rw [if_pos rfl, if_pos rfl]
    split_ifs with hc
    · have := eta2hat hh (j := j) (by rcases hj with rfl | rfl <;> omega)
      linarith
    · have := eta2 hh hj1
      linarith
  · rw [if_neg (by norm_num), if_neg (by norm_num)]
    split_ifs with hc
    · have := eta3hat hh (j := j) (by rcases hj with rfl | rfl <;> omega)
      linarith
    · have := L61i hh (a := 3) (by norm_num) hj1
      rw [if_neg (by norm_num)] at this
      linarith
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have := L61i hh (a := d) hd hj1
    rw [if_neg (by omega)] at this
    linarith

theorem eta_nonneg (hh : IsAdmissible h) (d c1 c2 : ℕ) : 0 ≤ eta h d c1 c2 := by
  have p2 := hpos hh (show 1 ≤ 2 by norm_num)
  unfold eta; split_ifs <;> linarith

/-- (20) with slack, `|X_A| = 2`, `a ≤ b` -/
theorem case2s_le (hh : IsAdmissible h) {a b c1 c2 : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hc1 : 1 ≤ c1)
    (hc2 : 1 ≤ c2) {pA pB1 pB2 : ℝ} (hpA : h a + h b ≤ pA)
    (hpB1 : h a + h (a - 1) + h b + h c1 ≤ pB1) (hpB2 : h b + h (b - 1) + h a + h c2 ≤ pB2) :
    2 * lam pA + lam pB1 + lam pB2 ≤ Hsum h a + Hsum h b + Aval h c1 + Aval h c2 -
      (if a = 2 then h 1 else 0) - (if b = 2 then h 1 else 0) - eta h a c1 c2 - eta h b c1 c2 := by
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
  have r1 := eta_ok hh ha hc1 hc2 (Or.inl rfl)
  have r2 := eta_ok hh hb hc1 hc2 (Or.inl rfl)
  have r3 := eta_ok hh ha hc1 hc2 (Or.inr rfl)
  have r4 := eta_ok hh hb hc1 hc2 (Or.inr rfl)
  have e1 : lam (h (b - 1) + 2 * h b + h c1 + (h (a - 1) - h (b - 1) + (h a - h b)) +
      (h a - h b)) = lam (h (a - 1) + 2 * h a + h c1) := by congr 1; ring
  have e2 : lam (h (b - 1) + 2 * h b + h c2 + (h a - h b) + (h (a - 1) - h (b - 1) +
      (h a - h b))) = lam (h (a - 1) + 2 * h a + h c2) := by congr 1; ring
  rw [e1] at i1
  rw [e2] at i2
  have key := comb hα hβ i1 i2 (T := Hsum h a - lam (2 * h a) - (if a = 2 then h 1 else 0) -
      eta h a c1 c2 + (Hsum h b - lam (2 * h b) - (if b = 2 then h 1 else 0) - eta h b c1 c2) +
      Aval h c1 + Aval h c2)
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

theorem eta_symm (d c1 c2 : ℕ) : eta h d c1 c2 = eta h d c2 c1 := by
  unfold eta
  have : (2 ≤ c1 ∧ 2 ≤ c2) ↔ (2 ≤ c2 ∧ 2 ≤ c1) := and_comm
  simp only [this]

theorem case2s (hh : IsAdmissible h) {a b c1 c2 : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc1 : 1 ≤ c1)
    (hc2 : 1 ≤ c2) {pA pB1 pB2 : ℝ} (hpA : h a + h b ≤ pA)
    (hpB1 : h a + h (a - 1) + h b + h c1 ≤ pB1) (hpB2 : h b + h (b - 1) + h a + h c2 ≤ pB2) :
    2 * lam pA + lam pB1 + lam pB2 ≤ Hsum h a + Hsum h b + Aval h c1 + Aval h c2 -
      (if a = 2 then h 1 else 0) - (if b = 2 then h 1 else 0) - eta h a c1 c2 - eta h b c1 c2 := by
  rcases le_total a b with hab | hba
  · exact case2s_le hh ha hab hc1 hc2 hpA hpB1 hpB2
  · have := case2s_le hh hb hba hc2 hc1 (pA := pA) (by linarith) hpB2 hpB1
    rw [eta_symm (c1 := c2), eta_symm (c1 := c2) (d := a)] at this
    linarith

end adm

section cover
variable {h : ℕ → ℝ}

theorem slack_cover (hh : IsAdmissible h) {am bm aw bw c1m c2m c1w c2w : ℕ}
    (h1m : 1 ≤ c1m) (h2m : 1 ≤ c2m) (h1w : 1 ≤ c1w) (h2w : 1 ≤ c2w)
    (g1 : c1m = 1 ↔ aw = 2) (g2 : c1w = 1 ↔ am = 2) (g3 : c2m = 1 ↔ bw = 2) (g4 : c2w = 1 ↔ bm = 2)
    (h3 : am = 3 ∨ bm = 3 ∨ aw = 3 ∨ bw = 3) :
    (if 2 ≤ c1m then h 2 else 0) + (if 2 ≤ c2m then h 2 else 0) +
        ((if 2 ≤ c1w then h 2 else 0) + (if 2 ≤ c2w then h 2 else 0)) ≤
      eta h am c1m c2m + eta h bm c1m c2m + eta h aw c1w c2w + eta h bw c1w c2w := by
  have p2 := hpos hh (show 1 ≤ 2 by norm_num)
  have n1 := eta_nonneg hh am c1m c2m
  have n2 := eta_nonneg hh bm c1m c2m
  have n3 := eta_nonneg hh aw c1w c2w
  have n4 := eta_nonneg hh bw c1w c2w
  have L2 : ∀ d c1 c2, d = 2 → h 2 ≤ eta h d c1 c2 := by
    intro d c1 c2 hd; unfold eta; rw [if_pos hd]; split_ifs <;> linarith
  have L2' : ∀ d c1 c2, d = 2 → 2 ≤ c1 → 2 ≤ c2 → 3 * h 2 ≤ eta h d c1 c2 := by
    intro d c1 c2 hd h1 h2; unfold eta; rw [if_pos hd, if_pos ⟨h1, h2⟩]
  have L3 : ∀ d c1 c2, d = 3 → 2 ≤ c1 → 2 ≤ c2 → 4 * h 2 ≤ eta h d c1 c2 := by
    intro d c1 c2 hd h1 h2; unfold eta; rw [if_neg (by omega), if_pos ⟨hd, h1, h2⟩]
  have F1 : (if 2 ≤ c1m then 0 else h 2) ≤ eta h aw c1w c2w := by
    split_ifs with k; · exact n3
    · exact L2 _ _ _ (g1.mp (by omega))
  have F2 : (if 2 ≤ c1w then 0 else h 2) ≤ eta h am c1m c2m := by
    split_ifs with k; · exact n1
    · exact L2 _ _ _ (g2.mp (by omega))
  have F3 : (if 2 ≤ c2m then 0 else h 2) ≤ eta h bw c1w c2w := by
    split_ifs with k; · exact n4
    · exact L2 _ _ _ (g3.mp (by omega))
  have F4 : (if 2 ≤ c2w then 0 else h 2) ≤ eta h bm c1m c2m := by
    split_ifs with k; · exact n2
    · exact L2 _ _ _ (g4.mp (by omega))
  have G1 : (if ¬ 2 ≤ c1w ∧ 2 ≤ c1m ∧ 2 ≤ c2m then 3 * h 2 else 0) ≤ eta h am c1m c2m := by
    split_ifs with k; · exact L2' _ _ _ (g2.mp (by omega)) k.2.1 k.2.2
    · exact n1
  have G2 : (if ¬ 2 ≤ c2w ∧ 2 ≤ c1m ∧ 2 ≤ c2m then 3 * h 2 else 0) ≤ eta h bm c1m c2m := by
    split_ifs with k; · exact L2' _ _ _ (g4.mp (by omega)) k.2.1 k.2.2
    · exact n2
  have G3 : (if ¬ 2 ≤ c1m ∧ 2 ≤ c1w ∧ 2 ≤ c2w then 3 * h 2 else 0) ≤ eta h aw c1w c2w := by
    split_ifs with k; · exact L2' _ _ _ (g1.mp (by omega)) k.2.1 k.2.2
    · exact n3
  have G4 : (if ¬ 2 ≤ c2m ∧ 2 ≤ c1w ∧ 2 ≤ c2w then 3 * h 2 else 0) ≤ eta h bw c1w c2w := by
    split_ifs with k; · exact L2' _ _ _ (g3.mp (by omega)) k.2.1 k.2.2
    · exact n4
  have H : (if 2 ≤ c1m ∧ 2 ≤ c2m ∧ 2 ≤ c1w ∧ 2 ≤ c2w then 4 * h 2 else 0) ≤
      eta h am c1m c2m + eta h bm c1m c2m + eta h aw c1w c2w + eta h bw c1w c2w := by
    split_ifs with k
    · obtain ⟨k1, k2, k3, k4⟩ := k
      rcases h3 with e | e | e | e
      · linarith [L3 _ _ _ e k1 k2]
      · linarith [L3 _ _ _ e k1 k2]
      · linarith [L3 _ _ _ e k3 k4]
      · linarith [L3 _ _ _ e k3 k4]
    · linarith
  by_cases k1 : 2 ≤ c1m <;> by_cases k2 : 2 ≤ c2m <;> by_cases k3 : 2 ≤ c1w <;>
    by_cases k4 : 2 ≤ c2w <;> simp only [k1, k2, k3, k4, if_true, if_false, and_true,
      not_true, not_false_eq_true, and_false] at F1 F2 F3 F4 G1 G2 G3 G4 H ⊢ <;> linarith

end cover

section final
variable {n : ℕ} (Q : Member n)

/-- Lemma 7.2's estimate: Lemma 6.2's two-association bound with the parents' slack retained. -/
theorem final72 (h : ℕ → ℝ) (hh : IsAdmissible h) {A : Fin Q.R} (hA : Q.IsInitialSwap A)
    {u v : Fin n} (huv : u ≠ v) (hp : Q.participants A = {u, v}) (hu : Q.IsFirst u A)
    (hv : Q.IsFirst v A) (x1 : Fin n) (B1 : Fin Q.R) (hs1 : Assoc Q A x1 u v B1)
    (x2 : Fin n) (B2 : Fin Q.R) (hs2 : Assoc Q A x2 v u B2) :
    Q.DStar h A ≤ (1 / 2) * (((if 2 ≤ Q.dL .man x1 then h 2 else 0) +
        (if 2 ≤ Q.dL .man x2 then h 2 else 0)) + ((if 2 ≤ Q.dL .woman x1 then h 2 else 0) +
        (if 2 ≤ Q.dL .woman x2 then h 2 else 0))) -
      (1 / 2) * (eta h (Q.dL .man u) (Q.dL .man x1) (Q.dL .man x2) +
        eta h (Q.dL .man v) (Q.dL .man x1) (Q.dL .man x2) +
        eta h (Q.dL .woman v) (Q.dL .woman x1) (Q.dL .woman x2) +
        eta h (Q.dL .woman u) (Q.dL .woman x1) (Q.dL .woman x2)) := by
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
  rw [DStar_eq Q h huv hp hu hv, hX, Finset.sum_pair hx12, Finset.sum_pair hx12,
    atFirst_eq Q hs1.1, atFirst_eq Q hs2.1]
  obtain ⟨bm, dmu, dmv⟩ := initial_bound Q h hnn A u v huv hp hu hv .man
  obtain ⟨bw, dwu, dwv⟩ := initial_bound Q h hnn A u v huv hp hu hv .woman
  obtain ⟨b1m, b1w, dmu2, dwv2, -, -, dmx1, dwx1⟩ := assoc_bound Q h hnn hs1
  obtain ⟨b2m, b2w, dmv2, dwu2, -, -, dmx2, dwx2⟩ := assoc_bound Q h hnn hs2
  obtain ⟨g1, g2⟩ := assoc_deg Q hs1
  obtain ⟨g3, g4⟩ := assoc_deg Q hs2
  have cm := case2s hh dmu2 dmv2 dmx1 dmx2 bm b1m b2m
  have cw := case2s hh dwv2 dwu2 dwx1 dwx2 (pA := Q.pLoss h .woman A) (by linarith) b1w b2w
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

/-- Lemma 7.2 (the case used): if `|X_A| = 2` and some parent degree is three, `D*_A ≤ 0`. -/
theorem lemma72 (h : ℕ → ℝ) (hh : IsAdmissible h) {A : Fin Q.R} (hA : Q.IsInitialSwap A)
    {u v : Fin n} (huv : u ≠ v) (hp : Q.participants A = {u, v}) (hu : Q.IsFirst u A)
    (hv : Q.IsFirst v A) (x1 : Fin n) (B1 : Fin Q.R) (hs1 : Assoc Q A x1 u v B1)
    (x2 : Fin n) (B2 : Fin Q.R) (hs2 : Assoc Q A x2 v u B2)
    (h3 : Q.dL .man u = 3 ∨ Q.dL .man v = 3 ∨ Q.dL .woman v = 3 ∨ Q.dL .woman u = 3) :
    Q.DStar h A ≤ 0 := by
  have hnn : ∀ r, 1 ≤ r → 0 ≤ h r := fun r hr => (hpos hh hr).le
  have F := final72 Q h hh hA huv hp hu hv x1 B1 hs1 x2 B2 hs2
  obtain ⟨-, -, -, -, -, -, dmx1, dwx1⟩ := assoc_bound Q h hnn hs1
  obtain ⟨-, -, -, -, -, -, dmx2, dwx2⟩ := assoc_bound Q h hnn hs2
  obtain ⟨g1, g2⟩ := assoc_deg Q hs1
  obtain ⟨g3, g4⟩ := assoc_deg Q hs2
  have := slack_cover hh dmx1 dmx2 dwx1 dwx2 g1 g2 g3 g4 h3
  linarith

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

/-- Lemma 8.2 (i), `d = 1` -/
theorem delta_d1 (hh : IsAdmissible h) {p : ℝ} (hp : h 1 ≤ p) :
    h 2 ≤ Hsum h 1 + 2 * h 1 + (if 2 ≤ 1 then h 2 else 0) - lam p := by
  have p1 := hpos hh (le_refl 1)
  have a := lam_anti' p1 hp
  obtain ⟨-, -, H43⟩ := hh.2.2.2.2.2.1
  rw [if_neg (by norm_num), Hsum_one]
  linarith

/-- Lemma 8.2 (ii) -/
theorem delta_ii (hh : IsAdmissible h) {d : ℕ} (hd : 1 ≤ d) {p : ℝ} (hp : h 2 + h d ≤ p) :
    2 * h 2 < Hsum h d + 2 * h 1 + (if 2 ≤ d then h 2 else 0) - lam p := by
  have p1 := hpos hh (le_refl 1)
  have p2 := hpos hh (show 1 ≤ 2 by norm_num)
  obtain ⟨H41, -, -⟩ := hh.2.2.2.2.2.1
  rcases (show d = 1 ∨ 2 ≤ d by omega) with rfl | hd2
  · rw [if_neg (by norm_num), Hsum_one]
    have a := lam_anti' (by positivity) hp
    have b := num3 hh.2.2.1 p2 H41
    rw [add_comm] at b
    linarith
  · rw [if_pos hd2]
    have pd := hpos hh hd
    have hd2' : h d ≤ h 2 := hanti hh (by norm_num) hd2
    have a := lam_anti' (by positivity : 0 < 2 * h d) (by linarith : 2 * h d ≤ p)
    have c := hh.2.2.2.1 d hd2
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

/-- in the opposite description, a mover's new partner is held by a mover -/
theorem opp_mv' (s : Sex) (k : Fin Q.R) (m : Fin n) :
    mv Q s k m ↔ mv Q (opp s) k (pm Q s k.castSucc m) := by
  rw [opp_mv, Equiv.symm_apply_apply]

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

theorem le_antisymm' {a b : Fin Q.R} (h1 : Q.le a b) (h2 : Q.le b a) : a = b :=
  le_antisymm (le_idx Q h1) (le_idx Q h2)

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

theorem isDn_down_sub (k : Fin Q.R) : IsDn Q (Q.down k \ {k}) := by
  intro a ha b hb
  simp only [Finset.mem_sdiff, Finset.mem_singleton, mem_down'] at ha ⊢
  refine ⟨le_tr Q hb ha.1, fun hbk => ha.2 ?_⟩
  subst hbk
  exact le_antisymm' Q ha.1 hb

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

/-- at a step `G` whose proper predecessors lie in `D`, every mover holds its `D`-partner -/
theorem dp_at (hσ : DP Q s D σ) (hD : IsDn Q D) {G : Fin Q.R} (hG : G ∉ D)
    (hpred : ∀ j, Q.le j G → j ≠ G → j ∈ D) {ℓ : Fin n} (hm : mv Q s G ℓ) :
    σ ℓ = pm Q s G.castSucc ℓ := by
  apply hσ
  intro k hk
  simp only [Fin.val_castSucc]
  constructor
  · intro hkD
    by_contra hc
    rcases (not_lt.mp hc).lt_or_eq with h | h
    · exact hG (hD k hkD G (chain_le Q s hm hk (Fin.lt_def.mpr h)))
    · exact hG ((Fin.ext h) ▸ hkD)
  · intro hlt
    exact hpred k (chain_le Q s hk hm (Fin.lt_def.mpr hlt)) (Fin.ne_of_lt (Fin.lt_def.mpr hlt))

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

theorem rank_next (s : Sex) {ℓ : Fin n} {a b : Fin Q.R} (ha : mv Q s a ℓ) (hb : mv Q s b ℓ)
    (hab : a < b) (hgap : ∀ k, a < k → k < b → ¬ mv Q s k ℓ) :
    Q.rank s (Q.person s ℓ) b = Q.rank s (Q.person s ℓ) a + 1 := by
  rw [rank_eq, rank_eq]
  have : (Finset.univ.filter fun j => mv Q s j ℓ ∧ j ≤ b) =
      insert b (Finset.univ.filter fun j => mv Q s j ℓ ∧ j ≤ a) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨hj, hjb⟩
      rcases hjb.lt_or_eq with h | h
      · right; refine ⟨hj, not_lt.mp fun h' => hgap j h' h hj⟩
      · left; exact h
    · rintro (rfl | ⟨hj, hja⟩)
      · exact ⟨hb, le_refl _⟩
      · exact ⟨hj, hja.trans hab.le⟩
  rw [this, Finset.card_insert_of_notMem]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_le]
  exact fun _ => hab

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

/-- the last step has rank `d` -/
theorem exists_rank (s : Sex) {ℓ : Fin n} {a : Fin Q.R} (ha : mv Q s a ℓ)
    (hlt : Q.rank s (Q.person s ℓ) a < Q.dL s ℓ) :
    ∃ b, mv Q s b ℓ ∧ a < b ∧ ∀ k, a < k → k < b → ¬ mv Q s k ℓ := by
  classical
  have hne : (Finset.univ.filter fun j => mv Q s j ℓ ∧ a < j).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    apply absurd hlt
    rw [not_lt, rank_eq, dL_eq]
    apply Finset.card_le_card
    intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hj
    refine ⟨hj, not_lt.mp fun h => ?_⟩
    have : j ∈ (Finset.univ.filter fun j => mv Q s j ℓ ∧ a < j) := by simp [hj, h]
    rw [hc] at this; simp at this
  set b := (Finset.univ.filter fun j => mv Q s j ℓ ∧ a < j).min' hne
  have hb : b ∈ Finset.univ.filter fun j => mv Q s j ℓ ∧ a < j := Finset.min'_mem _ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  refine ⟨b, hb.1, hb.2, fun k h1 h2 hk => ?_⟩
  have : b ≤ k := Finset.min'_le _ _ (by simp [hk, h1])
  exact absurd h2 (not_lt.mpr this)

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

theorem pred_man {j k : Fin Q.R} (h : Q.le j k) (hne : j ≠ k) :
    ∃ ℓ F, mv Q .man k ℓ ∧ mv Q .man F ℓ ∧ F < k ∧ Q.le j F := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hc, hck, m, h1, h2⟩
  · exact absurd h.symm hne
  · exact ⟨m, c, h2, h1, hck, hc⟩

theorem pred_opp (s : Sex)
    (H : ∀ {j k : Fin Q.R}, Q.le j k → j ≠ k → ∃ ℓ F, mv Q s k ℓ ∧ mv Q s F ℓ ∧ F < k ∧ Q.le j F)
    {j k : Fin Q.R} (h : Q.le j k) (hne : j ≠ k) :
    ∃ ℓ F, mv Q (opp s) k ℓ ∧ mv Q (opp s) F ℓ ∧ F < k ∧ Q.le j F := by
  classical
  obtain ⟨ℓ, F0, hk, hF0, hlt, hj⟩ := H h hne
  have hne' : (Finset.univ.filter fun F => mv Q s F ℓ ∧ F < k).Nonempty := ⟨F0, by simp [hF0, hlt]⟩
  set F := (Finset.univ.filter fun F => mv Q s F ℓ ∧ F < k).max' hne'
  have hF : F ∈ Finset.univ.filter fun F => mv Q s F ℓ ∧ F < k := Finset.max'_mem _ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF
  have hF0F : F0 ≤ F := Finset.le_max' _ _ (by simp [hF0, hlt])
  have hc : pm Q s k.castSucc ℓ = pm Q s F.succ ℓ := by
    apply pm_const Q s ℓ F.succ k.castSucc (lt_succ_le hF.2)
    intro k' a1 a2 hk'
    have : k' ≤ F := Finset.le_max' _ _ (by simp [hk', lt_of_castSucc a2])
    simp at a1; rw [Fin.le_def] at this; omega
  refine ⟨pm Q s F.succ ℓ, F, ?_, ?_, hF.2, ?_⟩
  · rw [← hc]; exact (opp_mv' Q s k ℓ).mp hk
  · rw [mv_iff]
    simp only [pm_opp]
    intro he
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_eq] at he
    exact ((mv_iff Q s F ℓ).mp hF.1) he.symm
  · exact le_tr Q hj ((chain_le_iff Q s hF0 hF.1).mpr hF0F)

theorem pred (s : Sex) {j k : Fin Q.R} (h : Q.le j k) (hne : j ≠ k) :
    ∃ ℓ F, mv Q s k ℓ ∧ mv Q s F ℓ ∧ F < k ∧ Q.le j F := by
  cases s
  · exact pred_man Q h hne
  · exact pred_opp Q .man (pred_man Q) h hne

theorem lt_of_dn (s : Sex) {D : Finset (Fin Q.R)} (hD : IsDn Q D) {j G : Fin Q.R} {ℓ : Fin n}
    (hj : j ∈ D) (hG : G ∉ D) (hmj : mv Q s j ℓ) (hmG : mv Q s G ℓ) : j < G := by
  by_contra hc
  rcases (not_lt.mp hc).lt_or_eq with h | h
  · exact hG (hD j hj G (chain_le Q s hmG hmj h))
  · exact hG (h ▸ hj)

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

theorem card5 {p q x y z : Fin n} (h1 : p ≠ q) (h2 : p ≠ x) (h3 : p ≠ y) (h4 : p ≠ z) (h5 : q ≠ x)
    (h6 : q ≠ y) (h7 : q ≠ z) (h8 : x ≠ y) (h9 : x ≠ z) (h10 : y ≠ z) :
    ({p, q, x, y, z} : Finset (Fin n)).card = 5 := by
  rw [Finset.card_insert_of_notMem (by simp [h1, h2, h3, h4]), card4 h5 h6 h7 h8 h9 h10]

end tools2

section AS
variable {Q : Member n} {s : Sex} {A B : Fin Q.R} {x p q : Fin n}

theorem AS.mvA1 (h : AS Q s A x p q B) : mv Q s A p := (h.mA p).mpr (Or.inl rfl)
theorem AS.mvA2 (h : AS Q s A x p q B) : mv Q s A q := (h.mA q).mpr (Or.inr rfl)
theorem AS.mvB1 (h : AS Q s A x p q B) : mv Q s B p := (h.mB p).mpr (Or.inl rfl)
theorem AS.mvB2 (h : AS Q s A x p q B) : mv Q s B x := (h.mB x).mpr (Or.inr rfl)

theorem AS.x_first (h : AS Q s A x p q B) : ∀ k, k < B → ¬ mv Q s k x :=
  (isFirst_mv Q s h.fx).2

theorem AS.p_first (h : AS Q s A x p q B) : ∀ k, k < A → ¬ mv Q s k p :=
  (isFirst_mv Q s h.fp).2

theorem AS.q_first (h : AS Q s A x p q B) : ∀ k, k < A → ¬ mv Q s k q :=
  (isFirst_mv Q s h.fq).2

theorem AS.pBc (h : AS Q s A x p q B) : pm Q s B.castSucc p = q := by
  rw [← h.pA1]
  exact pm_const Q s p A.succ B.castSucc (lt_succ_le h.lt) fun k a1 a2 =>
    h.gap k (lt_of_succ_le a1) (lt_of_castSucc a2)

theorem AS.pAc (h : AS Q s A x p q B) : pm Q s A.castSucc p = p := by
  have := pm_const Q s p 0 A.castSucc (Fin.zero_le _) fun k _ a2 => h.p_first k (lt_of_castSucc a2)
  rwa [pm_zero] at this

theorem AS.pSB (h : AS Q s A x p q B) : p ∈ Q.support B := by rw [h.supB]; simp

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

theorem opp_val {s : Sex} {t : Fin (Q.R + 1)} {a b : Fin n} (h : pm Q s t a = b) :
    pm Q (opp s) t b = a := by
  rw [pm_opp, Equiv.symm_apply_eq, h]

theorem of_opp_val {s : Sex} {t : Fin (Q.R + 1)} {a b : Fin n} (h : pm Q (opp s) t b = a) :
    pm Q s t a = b := by
  rw [pm_opp, Equiv.symm_apply_eq] at h; exact h.symm

theorem mv_of_new {s : Sex} {k : Fin Q.R} {a b c : Fin n} (hb : pm Q s k.castSucc b = c)
    (hab : a ≠ b) (ha : pm Q s k.succ a = c) : mv Q s k a := by
  rw [mv_iff, ha]
  intro he
  exact hab ((pm Q s k.castSucc).injective (he.trans hb.symm))

theorem pm_succ_le {k : Fin Q.R} {t : Fin (Q.R + 1)} (h : t ≤ k.castSucc) : t ≤ k.succ :=
  le_trans h (Fin.castSucc_le_succ k)

/-- `x`'s partner just before its second rotation -/
theorem AS.xCc (h : AS Q s A x p q B) {C : Fin Q.R} (hBC : B < C)
    (hgap : ∀ k, B < k → k < C → ¬ mv Q s k x) : pm Q s C.castSucc x = q := by
  rw [← h.pB2]
  exact pm_const Q s x B.succ C.castSucc (lt_succ_le hBC) fun k a1 a2 =>
    hgap k (lt_of_succ_le a1) (lt_of_castSucc a2)

/-- Lemma 7.3 (i): if `y` first moves at `C`, its next rotation has support of size at least five -/
theorem P4 (h : AS Q s A x p q B) {C : Fin Q.R} (hxC : mv Q s C x) (hBC : B < C)
    (hgap : ∀ k, B < k → k < C → ¬ mv Q s k x) {y : Fin n}
    (hK : Q.support C = {p, q, x, y}) (hyC : mv Q s C y)
    {F : Fin Q.R} (hyF : mv Q s F y) (hCF : C < F) (hgapF : ∀ k, C < k → k < F → ¬ mv Q s k y) :
    5 ≤ Q.s F := by
  have xc := h.xCc Q hBC hgap
  have oC : mv Q (opp s) C q := by have := (opp_mv' Q s C x).mp hxC; rwa [xc] at this
  have v0 : pm Q (opp s) 0 q = q := pm_zero Q _ q
  have v1 : pm Q (opp s) A.succ q = p := opp_val Q h.pA1
  have v2 : pm Q (opp s) B.succ q = x := opp_val Q h.pB2
  have hAC : A < C := h.lt.trans hBC
  have hAB := h.lt
  have mem := pm_mem_support Q (opp s) oC (t := C.succ) le_rfl
  rw [hK] at mem
  have n0 := norep Q (opp s) C q oC 0 C.succ (Fin.zero_le _) le_rfl
  have n1 := norep Q (opp s) C q oC A.succ C.succ (lt_succ_le hAC) le_rfl
  have n2 := norep Q (opp s) C q oC B.succ C.succ (lt_succ_le hBC) le_rfl
  rw [v0] at n0; rw [v1] at n1; rw [v2] at n2
  have vy : pm Q (opp s) C.succ q = y := by
    rcases mem4 mem with e | e | e | e
    · exact absurd e n1
    · exact absurd e n0
    · exact absurd e n2
    · exact e
  have yc : pm Q s F.castSucc y = q := by
    rw [← of_opp_val Q vy]
    exact pm_const Q s y C.succ F.castSucc (lt_succ_le hCF) fun k a1 a2 =>
      hgapF k (lt_of_succ_le a1) (lt_of_castSucc a2)
  have oF : mv Q (opp s) F q := by have := (opp_mv' Q s F y).mp hyF; rwa [yc] at this
  set w := pm Q (opp s) F.succ q
  have w0 := norep Q (opp s) F q oF 0 F.succ (Fin.zero_le _) le_rfl
  have w1 := norep Q (opp s) F q oF A.succ F.succ (lt_succ_le (hAC.trans hCF)) le_rfl
  have w2 := norep Q (opp s) F q oF B.succ F.succ (lt_succ_le (hBC.trans hCF)) le_rfl
  have w3 := norep Q (opp s) F q oF C.succ F.succ (lt_succ_le hCF) le_rfl
  rw [v0] at w0; rw [v1] at w1; rw [v2] at w2; rw [vy] at w3
  have wS := pm_mem_support Q (opp s) oF (t := F.succ) le_rfl
  have KS : Q.support C ⊆ Q.support F := support_mono Q (chain_le Q s hyC hyF hCF)
  rw [hK] at KS
  have hsub : insert w ({p, q, x, y} : Finset (Fin n)) ⊆ Q.support F :=
    Finset.insert_subset wS KS
  have hpq := h.pq; have hpx := h.px; have hqx := h.qx
  have hyp : y ≠ p := fun e => n1 (vy.trans e)
  have hyq : y ≠ q := fun e => n0 (vy.trans e)
  have hyx : y ≠ x := fun e => n2 (vy.trans e)
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨w1, w0, w2, w3⟩),
    card4 hpq hpx hyp.symm hqx hyq.symm hyx.symm] at this
  unfold Member.s; omega

end P34

section P3
variable (Q : Member n) {s : Sex} {A B : Fin Q.R} {x p q : Fin n}

theorem as_side {A' E : Fin Q.R} {y y' z' : Fin n} (hs : Assoc Q A' y y' z' E) (s : Sex) :
    ∃ p' q', AS Q s A' y p' q' E ∧ ((p' = y' ∧ q' = z') ∨ (p' = z' ∧ q' = y')) := by
  obtain ⟨h1, h2⟩ := as_of_assoc Q hs
  cases s
  · exact ⟨y', z', h1, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨z', y', h2, Or.inr ⟨rfl, rfl⟩⟩

/-- the initial swap of an exceptional label whose triple lies in `{p, q, x, y}` is `A` -/
theorem init_is_A (h : AS Q s A x p q B) {A' E : Fin Q.R} {y p' q' : Fin n}
    (h' : AS Q s A' y p' q' E) (hp' : p' = p ∨ p' = q ∨ p' = x) : A' = A := by
  rcases hp' with e | e | e
  · exact isFirst_unique Q h'.fp (e ▸ h.fp)
  · exact isFirst_unique Q h'.fp (e ▸ h.fq)
  · exfalso
    have hAB : A' = B := isFirst_unique Q h'.fp (e ▸ h.fx)
    rcases (h.mB q').mp (hAB ▸ h'.mvA2) with e2 | e2
    · have := isFirst_unique Q h.fp (e2 ▸ hAB ▸ h'.fq)
      exact absurd this (Fin.ne_of_lt h.lt)
    · exact h'.pq (e.trans e2.symm)

/-- Lemma 7.3 (iii): an exceptional fourth label shares the second rotation -/
theorem P3 (h : AS Q s A x p q B) {C : Fin Q.R} (hxC : mv Q s C x) (hBC : B < C)
    (hgap : ∀ k, B < k → k < C → ¬ mv Q s k x) {y : Fin n}
    (hK : Q.support C = {p, q, x, y}) (hyp : y ≠ p) (hyq : y ≠ q) (hyx : y ≠ x)
    (hexc : Q.IsExceptional y) :
    ∃ E, AS Q s A y q p E ∧ y ∈ Q.XA A ∧ E < C ∧ mv Q s C y ∧
      (∀ k, E < k → k < C → ¬ mv Q s k y) ∧ pm Q s C.succ x = p ∧ pm Q s C.succ y = q := by
  classical
  obtain ⟨E, hyE, hexcE⟩ := hexc
  obtain ⟨A', y', z', hAs⟩ := assoc_of_exc Q y E hyE hexcE
  obtain ⟨p', q', h', -⟩ := as_side Q hAs s
  have ySC : y ∈ Q.support C := by rw [hK]; simp
  have hEC : Q.le E C := h'.B_le ySC
  have subE := h'.supB_le ySC
  rw [hK] at subE
  have p'K : p' ∈ ({p, q, x, y} : Finset (Fin n)) := subE (by simp)
  have hA' : A' = A := by
    rcases mem4 p'K with e | e | e | e
    · exact init_is_A Q h h' (Or.inl e)
    · exact init_is_A Q h h' (Or.inr (Or.inl e))
    · exact init_is_A Q h h' (Or.inr (Or.inr e))
    · exact absurd e h'.px
  rw [hA'] at h' hAs
  have hyX : y ∈ Q.XA A := XA_of_assoc Q hAs
  have hp'q : p' = q := by
    rcases (h.mA p').mp h'.mvA1 with e | e
    · subst e; exact absurd (h.unique h').1 hyx.symm
    · exact e
  rw [hp'q] at h'
  have hq'p : q' = p := by
    rcases (h.mA q').mp h'.mvA2 with e | e
    · exact e
    · exact absurd e.symm h'.pq
  rw [hq'p] at h'
  -- now `h' : AS Q s A y q p E`
  have hAB := h.lt
  have hAE := h'.lt
  have hAC : A < C := hAB.trans hBC
  have xc := h.xCc Q hBC hgap
  -- woman `q` at `C`
  have oC : mv Q (opp s) C q := by have := (opp_mv' Q s C x).mp hxC; rwa [xc] at this
  have v0 : pm Q (opp s) 0 q = q := pm_zero Q _ q
  have v1 : pm Q (opp s) A.succ q = p := opp_val Q h.pA1
  have v2 : pm Q (opp s) B.succ q = x := opp_val Q h.pB2
  have mem := pm_mem_support Q (opp s) oC (t := C.succ) le_rfl
  rw [hK] at mem
  have n0 := norep Q (opp s) C q oC 0 C.succ (Fin.zero_le _) le_rfl
  have n1 := norep Q (opp s) C q oC A.succ C.succ (lt_succ_le hAC) le_rfl
  have n2 := norep Q (opp s) C q oC B.succ C.succ (lt_succ_le hBC) le_rfl
  rw [v0] at n0; rw [v1] at n1; rw [v2] at n2
  have vy : pm Q (opp s) C.succ q = y := by
    rcases mem4 mem with e | e | e | e
    · exact absurd e n1
    · exact absurd e n0
    · exact absurd e n2
    · exact e
  have yC : pm Q s C.succ y = q := of_opp_val Q vy
  have hyC : mv Q s C y := mv_of_new Q xc hyx yC
  have hEC' : E < C := by
    rcases (le_idx Q hEC).lt_or_eq with e | e
    · exact e
    · exfalso; subst e
      rcases (h'.mB x).mp hxC with e2 | e2
      · exact h.qx e2.symm
      · exact hyx e2.symm
  -- no rotation of `y` strictly between `E` and `C`
  have hgapy : ∀ k, E < k → k < C → ¬ mv Q s k y := by
    intro k0 hk1 hk2 hk3
    have hne : (Finset.univ.filter fun k => E < k ∧ k < C ∧ mv Q s k y).Nonempty :=
      ⟨k0, by simp [hk1, hk2, hk3]⟩
    set F := (Finset.univ.filter fun k => E < k ∧ k < C ∧ mv Q s k y).min' hne
    have hF : F ∈ Finset.univ.filter fun k => E < k ∧ k < C ∧ mv Q s k y := Finset.min'_mem _ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF
    have yF : pm Q s F.castSucc y = p := by
      rw [← h'.pB2]
      exact pm_const Q s y E.succ F.castSucc (lt_succ_le hF.1) fun k a1 a2 hk =>
        absurd (Finset.min'_le _ k (by simp [lt_of_succ_le a1, (lt_of_castSucc a2).trans hF.2.1, hk]))
          (not_le.mpr (lt_of_castSucc a2))
    have oF : mv Q (opp s) F p := by have := (opp_mv' Q s F y).mp hF.2.2; rwa [yF] at this
    have u0 : pm Q (opp s) 0 p = p := pm_zero Q _ p
    have u1 : pm Q (opp s) A.succ p = q := opp_val Q h.pA2
    have u2 : pm Q (opp s) E.succ p = y := opp_val Q h'.pB2
    have m0 := norep Q (opp s) F p oF 0 F.succ (Fin.zero_le _) le_rfl
    have m1 := norep Q (opp s) F p oF A.succ F.succ (lt_succ_le (hAE.trans hF.1)) le_rfl
    have m2 := norep Q (opp s) F p oF E.succ F.succ (lt_succ_le hF.1) le_rfl
    rw [u0] at m0; rw [u1] at m1; rw [u2] at m2
    have memF := pm_mem_support Q (opp s) oF (t := F.succ) le_rfl
    have FC := support_mono Q (chain_le Q s hF.2.2 hyC hF.2.1)
    rw [hK] at FC
    have vx : pm Q (opp s) F.succ p = x := by
      rcases mem4 (FC memF) with e | e | e | e
      · exact absurd e m0
      · exact absurd e m1
      · exact e
      · exact absurd e m2
    have xF : mv Q s F x := mv_of_new Q yF hyx.symm (of_opp_val Q vx)
    rcases lt_trichotomy F B with e | e | e
    · exact h.x_first F e xF
    · subst e
      rcases (h.mB y).mp hF.2.2 with e2 | e2
      · exact hyp e2
      · exact hyx e2
    · exact hgap F e hF.2.1 xF
  -- the opposite person `p` at `C`
  have yc : pm Q s C.castSucc y = p := by
    rw [← h'.pB2]
    exact pm_const Q s y E.succ C.castSucc (lt_succ_le hEC') fun k a1 a2 =>
      hgapy k (lt_of_succ_le a1) (lt_of_castSucc a2)
  have oC' : mv Q (opp s) C p := by have := (opp_mv' Q s C y).mp hyC; rwa [yc] at this
  have u0 : pm Q (opp s) 0 p = p := pm_zero Q _ p
  have u1 : pm Q (opp s) A.succ p = q := opp_val Q h.pA2
  have u2 : pm Q (opp s) E.succ p = y := opp_val Q h'.pB2
  have m0 := norep Q (opp s) C p oC' 0 C.succ (Fin.zero_le _) le_rfl
  have m1 := norep Q (opp s) C p oC' A.succ C.succ (lt_succ_le hAC) le_rfl
  have m2 := norep Q (opp s) C p oC' E.succ C.succ (lt_succ_le hEC') le_rfl
  rw [u0] at m0; rw [u1] at m1; rw [u2] at m2
  have memC := pm_mem_support Q (opp s) oC' (t := C.succ) le_rfl
  rw [hK] at memC
  have vx : pm Q (opp s) C.succ p = x := by
    rcases mem4 memC with e | e | e | e
    · exact absurd e m0
    · exact absurd e m1
    · exact e
    · exact absurd e m2
  exact ⟨E, h', hyX, hEC', hyC, hgapy, of_opp_val Q vx, yC⟩

end P3

section P5
variable (Q : Member n) {s : Sex} {A B : Fin Q.R} {x p q : Fin n}

theorem first_le {y : Fin n} {γ k : Fin Q.R} (s : Sex) (hf : Q.IsFirst y γ) (hk : y ∈ Q.support k) :
    Q.le γ k := by
  rw [support_iff Q s] at hk
  obtain ⟨j, hj, hm⟩ := hk
  have hγj : γ ≤ j := not_lt.mp fun hl => (isFirst_mv Q s hf).2 j hl hm
  exact le_tr Q ((chain_le_iff Q s (isFirst_mv Q s hf).1 hm).mpr hγj) hj

/-- Lemma 7.3 (ii) and the observation after it: if `y` first moves strictly before `C`, the third
rotation of `x` has support of size at least six, or a first rotation of size at least five contains
`S(C)`. -/
theorem P5 (h : AS Q s A x p q B) {C : Fin Q.R} (hxC : mv Q s C x) (hBC : B < C)
    (hgap : ∀ k, B < k → k < C → ¬ mv Q s k x) {y : Fin n}
    (hK : Q.support C = {p, q, x, y}) (hyp : y ≠ p) (hyq : y ≠ q) (hyx : y ≠ x)
    {γ : Fin Q.R} (hyγ : Q.IsFirst y γ) (hγC : γ ≠ C) (hSγ : Q.support γ = Q.support C)
    {τ : Fin Q.R} (hxτ : mv Q s τ x) (hCτ : C < τ) :
    6 ≤ Q.s τ ∨ ∃ G z, Q.IsFirst z G ∧ z ∉ Q.support C ∧ insert z (Q.support C) ⊆ Q.support G := by
  classical
  have inK : ∀ m, m ∈ Q.support C → m = p ∨ m = q ∨ m = x ∨ m = y := fun m hm => by
    rw [hK] at hm; exact mem4 hm
  have Kp : p ∈ Q.support C := by rw [hK]; simp
  have Kq : q ∈ Q.support C := by rw [hK]; simp
  have Kx : x ∈ Q.support C := by rw [hK]; simp
  have Ky : y ∈ Q.support C := by rw [hK]; simp
  have hpq := h.pq; have hpx := h.px; have hqx := h.qx
  obtain ⟨my, ny⟩ := isFirst_mv Q s hyγ
  have hγleC : Q.le γ C := first_le Q s hyγ Ky
  have hγC' : γ < C := lt_of_le_of_ne (le_idx Q hγleC) hγC
  have BleG : Q.le B γ := h.B_le (by rw [hSγ]; exact Kx)
  have hBγ : B < γ := by
    refine lt_of_le_of_ne (le_idx Q BleG) fun e => ?_
    rw [← e] at my
    rcases (h.mB y).mp my with e2 | e2
    · exact hyp e2
    · exact hyx e2
  have hAB := h.lt
  have hAγ : A < γ := hAB.trans hBγ
  have nxγ : ¬ mv Q s γ x := fun hm => hgap γ hBγ hγC' hm
  -- the downset `↓γ \ {γ}`
  set D' := Q.down γ \ {γ} with hD'def
  have hD' : IsDn Q D' := isDn_down_sub Q γ
  have memD' : ∀ j, Q.le j γ → j ≠ γ → j ∈ D' := fun j h1 h2 => by
    simp only [hD'def, Finset.mem_sdiff, Finset.mem_singleton, mem_down_iff]; exact ⟨h1, h2⟩
  have AD' : A ∈ D' := memD' A (le_tr Q h.le BleG) (Fin.ne_of_lt hAγ)
  have BD' : B ∈ D' := memD' B BleG (Fin.ne_of_lt hBγ)
  have γD' : γ ∉ D' := by simp [hD'def]
  have sup' : ∀ m, (∃ j ∈ D', mv Q s j m) → m = p ∨ m = q ∨ m = x := by
    rintro m ⟨j, hj, hm⟩
    simp only [hD'def, Finset.mem_sdiff, Finset.mem_singleton, mem_down_iff] at hj
    have : m ∈ Q.support C := by
      rw [← hSγ, support_iff Q s]; exact ⟨j, hj.1, hm⟩
    rcases inK m this with e | e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
    · exfalso; rw [e] at hm
      have hγj : γ ≤ j := not_lt.mp fun hl => ny j hl hm
      exact hj.2 (le_antisymm (le_idx Q hj.1) hγj)
  obtain ⟨σ', hσ'⟩ := down_perm Q s hD'
  have s'p : σ' p = x := by
    have p1 : σ' p ≠ p := by
      have := dp_ne Q hσ' hD' AD' h.mvA1 (Fin.zero_le _); rwa [pm_zero] at this
    have p2 : σ' p ≠ q := by
      have := dp_ne Q hσ' hD' BD' h.mvB1 (t1 := A.succ) (lt_succ_le hAB); rwa [h.pA1] at this
    rcases sup' _ (dp_mem Q hσ' ⟨A, AD', h.mvA1⟩) with e | e | e
    · exact absurd e p1
    · exact absurd e p2
    · exact e
  have s'q : σ' q = p := by
    have q1 : σ' q ≠ q := by
      have := dp_ne Q hσ' hD' AD' h.mvA2 (Fin.zero_le _); rwa [pm_zero] at this
    rcases sup' _ (dp_mem Q hσ' ⟨A, AD', h.mvA2⟩) with e | e | e
    · exact e
    · exact absurd e q1
    · exact absurd (σ'.injective (e.trans s'p.symm)) hpq.symm
  have predγ : ∀ j, Q.le j γ → j ≠ γ → j ∈ D' := memD'
  -- `p` moves at `γ`
  have pγ : mv Q s γ p := by
    by_contra hpγ
    obtain ⟨ℓ, F, hℓγ, hℓF, hFγ, hBF⟩ := pred Q s BleG (Fin.ne_of_lt hBγ)
    have ℓK : ℓ ∈ Q.support C := by rw [← hSγ]; exact mem_support_self Q s hℓγ
    rcases inK ℓ ℓK with e | e | e | e
    · rw [e] at hℓγ; exact hpγ hℓγ
    · rw [e] at hℓF hℓγ
      have FD' : F ∈ D' := memD' F (chain_le Q s hℓF hℓγ hFγ) (Fin.ne_of_lt hFγ)
      rcases eq_or_ne F A with eF | eF
      · rw [eF] at hBF; exact absurd (le_idx Q hBF) (not_le.mpr hAB)
      · have hAF : A < F := lt_of_le_of_ne (not_lt.mp fun hl => h.q_first F hl hℓF) (Ne.symm eF)
        have := dp_ne Q hσ' hD' FD' hℓF (t1 := A.succ) (lt_succ_le hAF)
        rw [h.pA2] at this; exact this s'q
    · rw [e] at hℓγ; exact nxγ hℓγ
    · rw [e] at hℓF; exact ny F hFγ hℓF
  have pγc : pm Q s γ.castSucc p = x := by
    rw [← s'p]; exact (dp_at Q hσ' hD' γD' predγ pγ).symm
  -- the downset `↓C`
  set D := Q.down C with hDdef
  have hD : IsDn Q D := isDn_down Q C
  have AD : A ∈ D := (mem_down_iff Q C A).mpr (le_tr Q h.le (le_tr Q BleG hγleC))
  have BD : B ∈ D := (mem_down_iff Q C B).mpr (le_tr Q BleG hγleC)
  have γD : γ ∈ D := (mem_down_iff Q C γ).mpr hγleC
  have CD : C ∈ D := (mem_down_iff Q C C).mpr (le_rfl' Q C)
  obtain ⟨σ, hσ⟩ := down_perm Q s hD
  have sp : σ p = y := by
    have a1 : σ p ≠ p := by
      have := dp_ne Q hσ hD AD h.mvA1 (Fin.zero_le _); rwa [pm_zero] at this
    have a2 : σ p ≠ q := by
      have := dp_ne Q hσ hD BD h.mvB1 (t1 := A.succ) (lt_succ_le hAB); rwa [h.pA1] at this
    have a3 : σ p ≠ x := by
      have := dp_ne Q hσ hD γD pγ (t1 := B.succ) (lt_succ_le hBγ); rwa [h.pB1] at this
    rcases inK _ (dp_down_mem Q hσ Kp) with e | e | e | e
    · exact absurd e a1
    · exact absurd e a2
    · exact absurd e a3
    · exact e
  have sx : σ x = p := by
    have a1 : σ x ≠ x := by
      have := dp_ne Q hσ hD BD h.mvB2 (Fin.zero_le _); rwa [pm_zero] at this
    have a2 : σ x ≠ q := by
      have := dp_ne Q hσ hD CD hxC (t1 := B.succ) (lt_succ_le hBC); rwa [h.pB2] at this
    rcases inK _ (dp_down_mem Q hσ Kx) with e | e | e | e
    · exact e
    · exact absurd e a2
    · exact absurd e a1
    · exact absurd (σ.injective (e.trans sp.symm)) hpx.symm
  have sq : σ q = x := by
    have a1 : σ q ≠ q := by
      have := dp_ne Q hσ hD AD h.mvA2 (Fin.zero_le _); rwa [pm_zero] at this
    rcases inK _ (dp_down_mem Q hσ Kq) with e | e | e | e
    · exact absurd (σ.injective (e.trans sx.symm)) hqx
    · exact absurd e a1
    · exact e
    · exact absurd (σ.injective (e.trans sp.symm)) hpq.symm
  have sy : σ y = q := by
    have a1 : σ y ≠ y := by
      have := dp_ne Q hσ hD γD my (Fin.zero_le _); rwa [pm_zero] at this
    rcases inK _ (dp_down_mem Q hσ Ky) with e | e | e | e
    · exact absurd (σ.injective (e.trans sx.symm)) hyx
    · exact e
    · exact absurd (σ.injective (e.trans sq.symm)) hyq
    · exact absurd e a1
  -- the first rotation `G` of `↓τ` outside `↓C`
  have Cleτ : Q.le C τ := chain_le Q s hxC hxτ hCτ
  have τD : τ ∉ D := fun hm => absurd (le_idx Q ((mem_down_iff Q C τ).mp hm)) (not_le.mpr hCτ)
  have hUne : (Q.down τ \ D).Nonempty := ⟨τ, by simp [τD, mem_down_iff, le_rfl' Q τ]⟩
  set G := (Q.down τ \ D).min' hUne
  have hGU : G ∈ Q.down τ \ D := Finset.min'_mem _ _
  rw [Finset.mem_sdiff, mem_down_iff] at hGU
  obtain ⟨GleT, GD⟩ := hGU
  have predG : ∀ j, Q.le j G → j ≠ G → j ∈ D := by
    intro j hj hne
    by_contra hjD
    have hjU : j ∈ Q.down τ \ D := by
      rw [Finset.mem_sdiff, mem_down_iff]; exact ⟨le_tr Q hj GleT, hjD⟩
    have := Finset.min'_le _ _ hjU
    exact hne (le_antisymm (le_idx Q hj) this)
  have supG : ∀ m, m ∈ Q.support G → m ∈ Q.support C ∨ mv Q s G m := by
    intro m hm
    rw [support_iff Q s] at hm
    obtain ⟨j, hj, hmj⟩ := hm
    rcases eq_or_ne j G with e | e
    · right; rw [← e]; exact hmj
    · left; rw [support_iff Q s]; exact ⟨j, (mem_down_iff Q C j).mp (predG j hj e), hmj⟩
  have cur : ∀ ℓ, mv Q s G ℓ → pm Q s G.castSucc ℓ = σ ℓ := fun ℓ hℓ =>
    (dp_at Q hσ hD GD predG hℓ).symm
  -- history facts
  have pVals : mv Q s G p → A < G ∧ B < G := fun hm =>
    ⟨lt_of_dn Q s hD AD GD h.mvA1 hm, lt_of_dn Q s hD BD GD h.mvB1 hm⟩
  -- `G` has a mover outside `K`
  have hZ : ∃ z, mv Q s G z ∧ z ∉ Q.support C := by
    by_contra hZ
    push Not at hZ
    have supG' : ∀ m, m ∈ Q.support G → m ∈ Q.support C := fun m hm => by
      rcases supG m hm with h1 | h1
      · exact h1
      · exact hZ m h1
    have newIn : ∀ ℓ, mv Q s G ℓ → pm Q s G.succ ℓ ∈ Q.support C := fun ℓ hℓ =>
      supG' _ (pm_mem_support Q s hℓ le_rfl)
    have np : ¬ mv Q s G p := by
      intro hm
      obtain ⟨hAG, hBG⟩ := pVals hm
      have c := cur p hm; rw [sp] at c
      have n0 := norep Q s G p hm 0 G.succ (Fin.zero_le _) le_rfl
      have n1 := norep Q s G p hm A.succ G.succ (lt_succ_le hAG) le_rfl
      have n2 := norep Q s G p hm B.succ G.succ (lt_succ_le hBG) le_rfl
      have n3 := norep Q s G p hm G.castSucc G.succ le_rfl le_rfl
      rw [pm_zero] at n0; rw [h.pA1] at n1; rw [h.pB1] at n2; rw [c] at n3
      rcases inK _ (newIn p hm) with e | e | e | e
      · exact n0 e
      · exact n1 e
      · exact n2 e
      · exact n3 e
    have nyG : ¬ mv Q s G y := by
      intro hm
      have hγG : γ < G := lt_of_dn Q s hD γD GD my hm
      have c := cur y hm; rw [sy] at c
      have oG : mv Q (opp s) G q := by have := (opp_mv' Q s G y).mp hm; rwa [c] at this
      have n0 := norep Q (opp s) G q oG 0 G.succ (Fin.zero_le _) le_rfl
      have n1 := norep Q (opp s) G q oG A.succ G.succ (lt_succ_le (hAγ.trans hγG)) le_rfl
      have n2 := norep Q (opp s) G q oG B.succ G.succ (lt_succ_le (hBγ.trans hγG)) le_rfl
      have n3 := norep Q (opp s) G q oG G.castSucc G.succ le_rfl le_rfl
      rw [pm_zero] at n0; rw [opp_val Q h.pA1] at n1; rw [opp_val Q h.pB2] at n2
      rw [opp_val Q c] at n3
      have mem := supG' _ (pm_mem_support Q (opp s) oG (t := G.succ) le_rfl)
      rcases inK _ mem with e | e | e | e
      · exact n1 e
      · exact n0 e
      · exact n2 e
      · exact n3 e
    have nxG : ¬ mv Q s G x := by
      intro hm
      have hCG : C < G := lt_of_dn Q s hD CD GD hxC hm
      obtain ⟨m, hmx, hmm, he⟩ := new_from' Q s hm
      have c := cur x hm; rw [sx] at c
      have n0 := norep Q s G x hm 0 G.succ (Fin.zero_le _) le_rfl
      have n1 := norep Q s G x hm B.succ G.succ (lt_succ_le (hBC.trans hCG)) le_rfl
      have n3 := norep Q s G x hm G.castSucc G.succ le_rfl le_rfl
      rw [pm_zero] at n0; rw [h.pB2] at n1; rw [c] at n3
      rcases inK _ (newIn x hm) with e | e | e | e
      · exact n3 e
      · exact n1 e
      · exact n0 e
      · rw [e, cur m hmm, ← sp] at he
        have := σ.injective he
        rw [← this] at hmm; exact np hmm
    obtain ⟨a, b, hab, ha, hb⟩ := exists_two_mv Q s G
    have onlyq : ∀ ℓ, mv Q s G ℓ → ℓ = q := by
      intro ℓ hℓ
      rcases inK ℓ (hZ ℓ hℓ) with e | e | e | e
      · rw [e] at hℓ; exact absurd hℓ np
      · exact e
      · rw [e] at hℓ; exact absurd hℓ nxG
      · rw [e] at hℓ; exact absurd hℓ nyG
    exact hab ((onlyq a ha).trans (onlyq b hb).symm)
  obtain ⟨z, hzG, hzK⟩ := hZ
  by_cases h6 : 6 ≤ Q.s τ
  · exact Or.inl h6
  right
  have zfirst : Q.IsFirst z G := by
    refine isFirst_of_mv Q s hzG fun k hk hmk => hzK ?_
    rw [support_iff Q s]
    exact ⟨k, (mem_down_iff Q C k).mp (predG k (chain_le Q s hmk hzG hk) (Fin.ne_of_lt hk)), hmk⟩
  refine ⟨G, z, zfirst, hzK, ?_⟩
  have zτ : z ∈ Q.support τ := support_mono Q GleT (mem_support_self Q s hzG)
  have Kτ : Q.support C ⊆ Q.support τ := support_mono Q Cleτ
  have sub5 : insert z (Q.support C) ⊆ Q.support τ := Finset.insert_subset zτ Kτ
  have hτeq : Q.support τ = insert z (Q.support C) := by
    symm
    apply Finset.eq_of_subset_of_card_le sub5
    rw [Finset.card_insert_of_notMem hzK, hK, card4 hpq hpx hyp.symm hqx hyq.symm hyx.symm]
    unfold Member.s at h6; omega
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_mv Q s G
  have movK : ∃ ℓ, mv Q s G ℓ ∧ ℓ ∈ Q.support C := by
    have aτ : a ∈ Q.support τ := support_mono Q GleT (mem_support_self Q s ha)
    have bτ : b ∈ Q.support τ := support_mono Q GleT (mem_support_self Q s hb)
    rw [hτeq, Finset.mem_insert] at aτ bτ
    rcases aτ with e | e
    · rcases bτ with e2 | e2
      · exact absurd (e.trans e2.symm) hab
      · exact ⟨b, hb, e2⟩
    · exact ⟨a, ha, e⟩
  obtain ⟨ℓ, hℓG, hℓK⟩ := movK
  have KG : Q.support C ⊆ Q.support G := by
    rcases inK ℓ hℓK with e | e | e | e
    · rw [e] at hℓG
      obtain ⟨hAG, hBG⟩ := pVals hℓG
      have c := cur p hℓG; rw [sp] at c
      intro m hm
      rcases inK m hm with e2 | e2 | e2 | e2 <;> rw [e2]
      · have := pm_mem_support Q s hℓG (t := 0) (Fin.zero_le _); rwa [pm_zero] at this
      · have := pm_mem_support Q s hℓG (t := A.succ) (pm_succ_le Q (lt_succ_le hAG))
        rwa [h.pA1] at this
      · have := pm_mem_support Q s hℓG (t := B.succ) (pm_succ_le Q (lt_succ_le hBG))
        rwa [h.pB1] at this
      · have := pm_mem_support Q s hℓG (t := G.castSucc) (Fin.castSucc_le_succ G)
        rwa [c] at this
    · rw [e] at hℓG
      have c := cur q hℓG; rw [sq] at c
      have oG : mv Q (opp s) G x := by have := (opp_mv' Q s G q).mp hℓG; rwa [c] at this
      have oγ : mv Q (opp s) γ x := by have := (opp_mv' Q s γ p).mp pγ; rwa [pγc] at this
      have hγG : γ < G := lt_of_dn Q (opp s) hD γD GD oγ oG
      rw [← hSγ]
      exact support_mono Q (chain_le Q (opp s) oγ oG hγG)
    · rw [e] at hℓG
      have hCG : C < G := lt_of_dn Q s hD CD GD hxC hℓG
      exact support_mono Q (chain_le Q s hxC hℓG hCG)
    · rw [e] at hℓG
      have hγG : γ < G := lt_of_dn Q s hD γD GD my hℓG
      have c := cur y hℓG; rw [sy] at c
      have oG : mv Q (opp s) G q := by have := (opp_mv' Q s G y).mp hℓG; rwa [c] at this
      intro m hm
      rcases inK m hm with e2 | e2 | e2 | e2 <;> rw [e2]
      · have := pm_mem_support Q (opp s) oG (t := A.succ)
          (pm_succ_le Q (lt_succ_le (hAγ.trans hγG)))
        rwa [opp_val Q h.pA1] at this
      · have := pm_mem_support Q (opp s) oG (t := 0) (Fin.zero_le _); rwa [pm_zero] at this
      · have := pm_mem_support Q (opp s) oG (t := B.succ)
          (pm_succ_le Q (lt_succ_le (hBγ.trans hγG)))
        rwa [opp_val Q h.pB2] at this
      · have := pm_mem_support Q (opp s) oG (t := G.castSucc) (Fin.castSucc_le_succ G)
        rwa [opp_val Q c] at this
  exact Finset.insert_subset (mem_support_self Q s hzG) KG

end P5

section P6
variable (Q : Member n) {s : Sex} {A B E : Fin Q.R} {x y p q : Fin n}

/-- the final assertion of Lemma 7.3 (iii) -/
theorem P6 (h : AS Q s A x p q B) (h' : AS Q s A y q p E) {C : Fin Q.R} (hxC : mv Q s C x)
    (hBC : B < C) (hgap : ∀ k, B < k → k < C → ¬ mv Q s k x) (hyC : y ∈ Q.support C)
    {z : Fin n} {G : Fin Q.R} (hzG : Q.IsFirst z G) (hSG : Q.support G = {p, q, x, z})
    (hzp : z ≠ p) (hzq : z ≠ q) (hzx : z ≠ x) (hyG : y ∉ Q.support G)
    {F : Fin Q.R} (hzF : mv Q s F z) (hGF : G < F) (hgapF : ∀ k, G < k → k < F → ¬ mv Q s k z) :
    5 ≤ Q.s F := by
  classical
  have hpq := h.pq; have hpx := h.px; have hqx := h.qx
  obtain ⟨mz, nz⟩ := isFirst_mv Q s hzG
  have xSG : x ∈ Q.support G := by rw [hSG]; simp
  have BleG : Q.le B G := h.B_le xSG
  have hBG : B ≠ G := fun e => by
    rw [← e] at mz
    rcases (h.mB z).mp mz with e2 | e2
    · exact hzp e2
    · exact hzx e2
  set D' := Q.down G \ {G} with hD'def
  have hD' : IsDn Q D' := isDn_down_sub Q G
  have memD' : ∀ j, Q.le j G → j ≠ G → j ∈ D' := fun j h1 h2 => by
    simp only [hD'def, Finset.mem_sdiff, Finset.mem_singleton, mem_down_iff]; exact ⟨h1, h2⟩
  have AD' : A ∈ D' := memD' A (le_tr Q h.le BleG) (fun e => by
    rw [e] at h; exact hBG (le_antisymm (le_idx Q BleG) h.lt.le))
  have BD' : B ∈ D' := memD' B BleG hBG
  have GD' : G ∉ D' := by simp [hD'def]
  have sup' : ∀ m, (∃ j ∈ D', mv Q s j m) → m = p ∨ m = q ∨ m = x := by
    rintro m ⟨j, hj, hm⟩
    simp only [hD'def, Finset.mem_sdiff, Finset.mem_singleton, mem_down_iff] at hj
    have : m ∈ Q.support G := by rw [support_iff Q s]; exact ⟨j, hj.1, hm⟩
    rw [hSG] at this
    rcases mem4 this with e | e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
    · exfalso; rw [e] at hm
      have hGj : G ≤ j := not_lt.mp fun hl => nz j hl hm
      exact hj.2 (le_antisymm (le_idx Q hj.1) hGj)
  obtain ⟨σ', hσ'⟩ := down_perm Q s hD'
  have s'p : σ' p = x := by
    have p1 : σ' p ≠ p := by
      have := dp_ne Q hσ' hD' AD' h.mvA1 (Fin.zero_le _); rwa [pm_zero] at this
    have p2 : σ' p ≠ q := by
      have := dp_ne Q hσ' hD' BD' h.mvB1 (t1 := A.succ) (lt_succ_le h.lt); rwa [h.pA1] at this
    rcases sup' _ (dp_mem Q hσ' ⟨A, AD', h.mvA1⟩) with e | e | e
    · exact absurd e p1
    · exact absurd e p2
    · exact e
  have predG : ∀ j, Q.le j G → j ≠ G → j ∈ D' := memD'
  have movG : ∀ ℓ, mv Q s G ℓ → ℓ = p ∨ ℓ = z := by
    intro ℓ hℓ
    have hℓS := mem_support_self Q s hℓ
    rw [hSG] at hℓS
    rcases mem4 hℓS with e | e | e | e
    · exact Or.inl e
    · exfalso; rw [e] at hℓ
      have hAG : A < G := lt_of_dn Q s hD' AD' GD' h.mvA2 hℓ
      have hEG : E ≤ G := not_lt.mp fun hl => h'.gap G hAG hl hℓ
      have : Q.le E G := (chain_le_iff Q s h'.mvB1 hℓ).mpr hEG
      exact hyG (support_mono Q this (mem_support_self Q s h'.mvB2))
    · exfalso; rw [e] at hℓ
      have hBG' : B < G := lt_of_dn Q s hD' BD' GD' h.mvB2 hℓ
      have hCG : C ≤ G := not_lt.mp fun hl => hgap G hBG' hl hℓ
      have : Q.le C G := (chain_le_iff Q s hxC hℓ).mpr hCG
      exact hyG (support_mono Q this hyC)
    · exact Or.inr e
  have pG : mv Q s G p := by
    obtain ⟨a, b, hab, ha, hb⟩ := exists_two_mv Q s G
    rcases movG a ha with e | e
    · rw [← e]; exact ha
    · rcases movG b hb with e2 | e2
      · rw [← e2]; exact hb
      · exact absurd (e.trans e2.symm) hab
  have pGc : pm Q s G.castSucc p = x := by
    rw [← s'p]; exact (dp_at Q hσ' hD' GD' predG pG).symm
  have zG1 : pm Q s G.succ z = x := by
    obtain ⟨m, hmz, hm, he⟩ := new_from' Q s mz
    rcases movG m hm with e | e
    · rw [he, e, pGc]
    · exact absurd e hmz
  have zc : pm Q s F.castSucc z = x := by
    rw [← zG1]
    exact pm_const Q s z G.succ F.castSucc (lt_succ_le hGF) fun k a1 a2 =>
      hgapF k (lt_of_succ_le a1) (lt_of_castSucc a2)
  have oF : mv Q (opp s) F x := by have := (opp_mv' Q s F z).mp hzF; rwa [zc] at this
  have hBG' : B < G := lt_of_le_of_ne (le_idx Q BleG) hBG
  have n0 := norep Q (opp s) F x oF 0 F.succ (Fin.zero_le _) le_rfl
  have n1 := norep Q (opp s) F x oF B.succ F.succ (lt_succ_le (hBG'.trans hGF)) le_rfl
  have n2 := norep Q (opp s) F x oF G.succ F.succ (lt_succ_le hGF) le_rfl
  rw [pm_zero] at n0; rw [opp_val Q h.pB1] at n1; rw [opp_val Q zG1] at n2
  have wS := pm_mem_support Q (opp s) oF (t := F.succ) le_rfl
  have GF : Q.support G ⊆ Q.support F := support_mono Q (chain_le Q s mz hzF hGF)
  rw [hSG] at GF
  unfold Member.s
  by_cases hwq : pm Q (opp s) F.succ x = q
  · have qF : mv Q s F q := mv_of_new Q zc hzq.symm (of_opp_val Q hwq)
    have hAF : A < F := (h.lt.trans hBG').trans hGF
    have hEF : E ≤ F := not_lt.mp fun hl => h'.gap F hAF hl qF
    have yF : y ∈ Q.support F :=
      support_mono Q ((chain_le_iff Q s h'.mvB1 qF).mpr hEF) (mem_support_self Q s h'.mvB2)
    have hyp : y ≠ p := h'.qx.symm
    have hyq : y ≠ q := h'.px.symm
    have hyx : y ≠ x := fun e => hyG (e ▸ xSG)
    have hyz : y ≠ z := fun e => hyG (e ▸ mem_support_self Q s mz)
    have sub : insert y ({p, q, x, z} : Finset (Fin n)) ⊆ Q.support F := Finset.insert_subset yF GF
    have := Finset.card_le_card sub
    rw [Finset.card_insert_of_notMem (by simp [hyp, hyq, hyx, hyz]),
      card4 hpq hpx hzp.symm hqx hzq.symm hzx.symm] at this
    omega
  · have sub : insert (pm Q (opp s) F.succ x) ({p, q, x, z} : Finset (Fin n)) ⊆ Q.support F :=
      Finset.insert_subset wS GF
    have := Finset.card_le_card sub
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨n1, hwq, n0, n2⟩),
      card4 hpq hpx hzp.symm hqx hzq.symm hzx.symm] at this
    omega

/-- Case 1: the third rotation of `x` leaves `K` -/
theorem third (h : AS Q s A x p q B) (h' : AS Q s A y q p E) {C : Fin Q.R} (hxC : mv Q s C x)
    (hEC : E < C) (hxCv : pm Q s C.succ x = p) {τ : Fin Q.R} (hxτ : mv Q s τ x) (hCτ : C < τ)
    (hgapτ : ∀ k, C < k → k < τ → ¬ mv Q s k x) :
    ∃ w, w ≠ p ∧ w ≠ q ∧ w ≠ x ∧ w ≠ y ∧ w ∈ Q.support τ := by
  have xc : pm Q s τ.castSucc x = p := by
    rw [← hxCv]
    exact pm_const Q s x C.succ τ.castSucc (lt_succ_le hCτ) fun k a1 a2 =>
      hgapτ k (lt_of_succ_le a1) (lt_of_castSucc a2)
  have oτ : mv Q (opp s) τ p := by have := (opp_mv' Q s τ x).mp hxτ; rwa [xc] at this
  have hAE := h'.lt
  have n0 := norep Q (opp s) τ p oτ 0 τ.succ (Fin.zero_le _) le_rfl
  have n1 := norep Q (opp s) τ p oτ A.succ τ.succ (lt_succ_le ((hAE.trans hEC).trans hCτ)) le_rfl
  have n2 := norep Q (opp s) τ p oτ E.succ τ.succ (lt_succ_le (hEC.trans hCτ)) le_rfl
  have n3 := norep Q (opp s) τ p oτ C.succ τ.succ (lt_succ_le hCτ) le_rfl
  rw [pm_zero] at n0; rw [opp_val Q h.pA2] at n1; rw [opp_val Q h'.pB2] at n2
  rw [opp_val Q hxCv] at n3
  exact ⟨_, n0, n1, n3, n2, pm_mem_support Q (opp s) oτ le_rfl⟩

/-- Case 1: if `x` stops after `C`, its partner (a parent) has degree three in the other description -/
theorem deg3 (h : AS Q s A x p q B) (h' : AS Q s A y q p E) {C : Fin Q.R} (hyC : mv Q s C y)
    (hEC : E < C) (hgapy : ∀ k, E < k → k < C → ¬ mv Q s k y) (hxCv : pm Q s C.succ x = p)
    (hno : ∀ k, C < k → ¬ mv Q s k x) : Q.dL (opp s) p = 3 := by
  classical
  have hAE := h'.lt
  have hAC := hAE.trans hEC
  rw [dL_eq]
  have hold' : ∀ k m, pm Q s k.castSucc m = p → (mv Q (opp s) k p ↔ mv Q s k m) := by
    intro k m hm; rw [opp_mv' Q s k m, hm]
  have key : (Finset.univ.filter fun j => mv Q (opp s) j p) = {A, E, C} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    have hold := hold' k
    constructor
    · intro hk
      rcases lt_trichotomy k A with e1 | e1 | e1
      · have c : pm Q s k.castSucc p = p := by
          have := pm_const Q s p 0 k.castSucc (Fin.zero_le _) fun k' _ a2 =>
            h.p_first k' ((lt_of_castSucc a2).trans e1)
          rwa [pm_zero] at this
        exact absurd ((hold p c).mp hk) (h.p_first k e1)
      · exact Or.inl e1
      rcases lt_trichotomy k E with e2 | e2 | e2
      · have c : pm Q s k.castSucc q = p := by
          rw [← h.pA2]
          exact pm_const Q s q A.succ k.castSucc (lt_succ_le e1) fun k' a1 a2 =>
            h'.gap k' (lt_of_succ_le a1) ((lt_of_castSucc a2).trans e2)
        exact absurd ((hold q c).mp hk) (h'.gap k e1 e2)
      · exact Or.inr (Or.inl e2)
      rcases lt_trichotomy k C with e3 | e3 | e3
      · have c : pm Q s k.castSucc y = p := by
          rw [← h'.pB2]
          exact pm_const Q s y E.succ k.castSucc (lt_succ_le e2) fun k' a1 a2 =>
            hgapy k' (lt_of_succ_le a1) ((lt_of_castSucc a2).trans e3)
        exact absurd ((hold y c).mp hk) (hgapy k e2 e3)
      · exact Or.inr (Or.inr e3)
      · have c : pm Q s k.castSucc x = p := by
          rw [← hxCv]
          exact pm_const Q s x C.succ k.castSucc (lt_succ_le e3) fun k' a1 _ =>
            hno k' (lt_of_succ_le a1)
        exact absurd ((hold x c).mp hk) (hno k e3)
    · rintro (e | e | e) <;> rw [e]
      · exact (hold' A p h.pAc).mpr h.mvA1
      · have c : pm Q s E.castSucc q = p := h'.pBc
        exact (hold' E q c).mpr h'.mvB1
      · have c : pm Q s C.castSucc y = p := by
          rw [← h'.pB2]
          exact pm_const Q s y E.succ C.castSucc (lt_succ_le hEC) fun k' a1 a2 =>
            hgapy k' (lt_of_succ_le a1) (lt_of_castSucc a2)
        exact (hold' C y c).mpr hyC
  rw [key, Finset.card_insert_of_notMem (by simp [Fin.ne_of_lt hAE, Fin.ne_of_lt hAC]),
    Finset.card_pair (Fin.ne_of_lt hEC)]

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

theorem triple {s : Sex} {A B : Fin Q.R} {x p q : Fin n} (h : AS Q s A x p q B)
    (hx : x ∈ Q.XA A) {S : Finset (Fin n)} (hS : ({p, q, x} : Finset (Fin n)) ⊆ S) :
    Q.HasTripleIn A S := by
  refine ⟨x, hx, ?_⟩
  rw [fgA Q h]
  intro w hw
  apply hS
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw ⊢
  tauto

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

/-- Case 2: a non-exceptional fourth label `y` of `S(C)` has an ordinary first rotation with
`S(b_y) = S(C)` -/
theorem case2_y {s : Sex} {A B C : Fin Q.R} {x p q y : Fin n} (h : AS Q s A x p q B)
    (hK : Q.support C = {p, q, x, y}) (hyp : y ≠ p) (hyq : y ≠ q) (hyx : y ≠ x)
    {γ : Fin Q.R} (hyγ : Q.IsFirst y γ) (hne : ¬ Q.IsExceptional y) :
    Q.firstGroup γ = {y} ∧ Q.IsOrdinary γ ∧ Q.support γ = Q.support C := by
  have Ky : y ∈ Q.support C := by rw [hK]; simp
  have γC : Q.support γ ⊆ Q.support C := support_mono Q (first_le Q s hyγ Ky)
  obtain ⟨my, -⟩ := isFirst_mv Q s hyγ
  have fg : Q.firstGroup γ = {y} := by
    ext w
    rw [mem_fg, Finset.mem_singleton]
    constructor
    · intro hw
      have wC := γC (mem_support_self Q s (isFirst_mv Q s hw).1)
      rw [hK] at wC
      rcases mem4 wC with e | e | e | e
      · rw [e] at hw
        have := isFirst_unique Q hw h.fp; rw [this] at my
        rcases (h.mA y).mp my with e2 | e2
        · exact absurd e2 hyp
        · exact absurd e2 hyq
      · rw [e] at hw
        have := isFirst_unique Q hw h.fq; rw [this] at my
        rcases (h.mA y).mp my with e2 | e2
        · exact absurd e2 hyp
        · exact absurd e2 hyq
      · rw [e] at hw
        have := isFirst_unique Q hw h.fx; rw [this] at my
        rcases (h.mB y).mp my with e2 | e2
        · exact absurd e2 hyp
        · exact absurd e2 hyx
      · exact e
    · intro e; rw [e]; exact hyγ
  obtain ⟨ho, h4⟩ := single_ord Q fg hne
  refine ⟨fg, ho, Finset.eq_of_subset_of_card_le γC ?_⟩
  rw [hK, card4 h.pq h.px hyp.symm h.qx hyq.symm hyx.symm]
  exact h4

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

/-- Case 1: a fifth label `z` of a third support is in `Z_A`, and `z` stops or its second support has
size at least five -/
theorem zlemma {s : Sex} {A B E C : Fin Q.R} {x y p q : Fin n} (h : AS Q s A x p q B)
    (h' : AS Q s A y q p E) (hxX : x ∈ Q.XA A) (hyX : y ∈ Q.XA A)
    (hxC : mv Q s C x) (hBC : B < C) (hgapx : ∀ k, B < k → k < C → ¬ mv Q s k x)
    (hyC : mv Q s C y) (hEC : E < C) (hgapy : ∀ k, E < k → k < C → ¬ mv Q s k y)
    (hK : Q.support C = {p, q, x, y})
    (hP0 : ∀ i, Q.IsOrdinary i → Q.HasTripleIn A (Q.support i) → Q.s i < 5)
    {z : Fin n} {G : Fin Q.R} (hzG : Q.IsFirst z G) (hzK : z ∉ Q.support C)
    (hGsub : Q.support G ⊆ insert z (Q.support C)) :
    Q.firstGroup G = {z} ∧ Q.IsOrdinary G ∧ Q.HasTripleIn A (Q.support G) ∧
      ∀ F, mv Q s F z → G < F → (∀ k, G < k → k < F → ¬ mv Q s k z) → 5 ≤ Q.s F := by
  classical
  have hpq := h.pq; have hpx := h.px; have hqx := h.qx
  have hyp : y ≠ p := h'.qx.symm
  have hyq : y ≠ q := h'.px.symm
  have hxy : x ≠ y := by
    intro e
    have hBE : B = E := isFirst_unique Q h.fx (by rw [e]; exact h'.fx)
    rcases (h.mB q).mp (by rw [hBE]; exact h'.mvB1) with e2 | e2
    · exact h.pq e2.symm
    · exact h.qx e2
  have hzp : z ≠ p := fun e => hzK (by rw [e, hK]; simp)
  have hzq : z ≠ q := fun e => hzK (by rw [e, hK]; simp)
  have hzx : z ≠ x := fun e => hzK (by rw [e, hK]; simp)
  have hzy : z ≠ y := fun e => hzK (by rw [e, hK]; simp)
  obtain ⟨mz, nz⟩ := isFirst_mv Q s hzG
  have inG : ∀ w, w ∈ Q.support G → w = z ∨ w = p ∨ w = q ∨ w = x ∨ w = y := by
    intro w hw
    have := hGsub hw
    rw [Finset.mem_insert, hK] at this
    rcases this with e | e
    · exact Or.inl e
    · exact Or.inr (mem4 e)
  -- the first group
  have fg : Q.firstGroup G = {z} := by
    ext w
    rw [mem_fg, Finset.mem_singleton]
    constructor
    · intro hw
      rcases inG w (mem_support_self Q s (isFirst_mv Q s hw).1) with e | e | e | e | e
      · exact e
      · rw [e] at hw; rw [isFirst_unique Q hw h.fp] at mz
        rcases (h.mA z).mp mz with e2 | e2 <;> [exact absurd e2 hzp; exact absurd e2 hzq]
      · rw [e] at hw; rw [isFirst_unique Q hw h.fq] at mz
        rcases (h.mA z).mp mz with e2 | e2 <;> [exact absurd e2 hzp; exact absurd e2 hzq]
      · rw [e] at hw; rw [isFirst_unique Q hw h.fx] at mz
        rcases (h.mB z).mp mz with e2 | e2 <;> [exact absurd e2 hzp; exact absurd e2 hzx]
      · rw [e] at hw; rw [isFirst_unique Q hw h'.fx] at mz
        rcases (h'.mB z).mp mz with e2 | e2 <;> [exact absurd e2 hzq; exact absurd e2 hzy]
    · intro e; rw [e]; exact hzG
  -- `z` is not exceptional
  have hne : ¬ Q.IsExceptional z := by
    rintro ⟨G', hzG', hexc⟩
    rw [isFirst_unique Q hzG' hzG] at hexc
    obtain ⟨A', y', z', hAs⟩ := assoc_of_exc Q z G hzG hexc
    obtain ⟨p', q', h'', -⟩ := as_side Q hAs s
    have p'G := h''.pSB
    have hA' : A' = A := by
      rcases inG p' p'G with e | e | e | e | e
      · exact absurd e h''.px
      · exact init_is_A Q h h'' (Or.inl e)
      · exact init_is_A Q h h'' (Or.inr (Or.inl e))
      · exact init_is_A Q h h'' (Or.inr (Or.inr e))
      · exact init_is_A Q h' h'' (Or.inr (Or.inr e))
    rw [hA'] at h''
    rcases (h.mA p').mp h''.mvA1 with e | e
    · rw [e] at h''; exact hzx (h.unique h'').1.symm
    · rw [e] at h''; exact hzy (h'.unique h'').1.symm
  obtain ⟨ho, h4⟩ := single_ord Q fg hne
  refine ⟨fg, ho, ?_⟩
  have xy : x ∈ Q.support G ∨ y ∈ Q.support G := by
    by_contra hc
    push Not at hc
    have sub : Q.support G ⊆ {z, p, q} := by
      intro w hw
      rcases inG w hw with e | e | e | e | e
      · rw [e]; simp
      · rw [e]; simp
      · rw [e]; simp
      · exact absurd (e ▸ hw) hc.1
      · exact absurd (e ▸ hw) hc.2
    have := Finset.card_le_card sub
    rw [card3 hzp hzq hpq] at this
    unfold Member.s at h4; omega
  rcases xy with hx | hy
  · have tr := triple Q h hxX (h.supB_le hx)
    refine ⟨tr, fun F hzF hGF hgapF => ?_⟩
    have h5 := hP0 G ho tr
    have sub : ({p, q, x, z} : Finset (Fin n)) ⊆ Q.support G := by
      intro w hw
      rcases mem4 hw with e | e | e | e <;> rw [e]
      · exact h.supB_le hx (by simp)
      · exact h.supB_le hx (by simp)
      · exact hx
      · exact mem_support_self Q s mz
    have hSG : Q.support G = {p, q, x, z} := by
      symm; apply Finset.eq_of_subset_of_card_le sub
      rw [card4 hpq hpx hzp.symm hqx hzq.symm hzx.symm]; unfold Member.s at h5; omega
    have hyG : y ∉ Q.support G := by
      rw [hSG]; simp [hyp, hyq, hxy.symm, hzy.symm]
    exact P6 Q h h' hxC hBC hgapx (by rw [hK]; simp) hzG hSG hzp hzq hzx hyG hzF hGF hgapF
  · have tr := triple Q h' hyX (h'.supB_le hy)
    refine ⟨tr, fun F hzF hGF hgapF => ?_⟩
    have h5 := hP0 G ho tr
    have sub : ({q, p, y, z} : Finset (Fin n)) ⊆ Q.support G := by
      intro w hw
      rcases mem4 hw with e | e | e | e <;> rw [e]
      · exact h'.supB_le hy (by simp)
      · exact h'.supB_le hy (by simp)
      · exact hy
      · exact mem_support_self Q s mz
    have hSG : Q.support G = {q, p, y, z} := by
      symm; apply Finset.eq_of_subset_of_card_le sub
      rw [card4 hpq.symm hyq.symm hzq.symm hyp.symm hzp.symm hzy.symm]
      unfold Member.s at h5; omega
    have hxG : x ∉ Q.support G := by
      rw [hSG]; simp [hpx.symm, hqx.symm, hxy, hzx.symm]
    exact P6 Q h' h hyC hEC hgapy (by rw [hK]; simp) hzG hSG hzq hzp hzy hxG hzF hGF hgapF

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

theorem Ex_ge (hh : IsAdmissible h) {A : Fin Q.R} {x : Fin n} (hx : x ∈ Q.XA A) (s : Sex)
    {i : Fin Q.R} (hi : mv Q s i x) (h2 : 2 ≤ Q.rank s (Q.person s x) i)
    (h3 : Q.rank s (Q.person s x) i ≤ 3) :
    ((Q.s i : ℝ) - 4) * h (Q.rank s (Q.person s x) i) ≤ Q.Ex h s x := by
  unfold Member.Ex
  apply Finset.single_le_sum (f := fun i => ((Q.s i : ℝ) - 4) * h (Q.rank s (Q.person s x) i))
    (Ex_term_nonneg Q h hh hx s)
  simp only [Finset.mem_filter]
  exact ⟨(mem_chainOf Q s _ i).mpr hi, h2, h3⟩

/-- `E_x` dominates its two specified terms -/
theorem Ex_ge2 (hh : IsAdmissible h) {A : Fin Q.R} {x : Fin n} (hx : x ∈ Q.XA A) (s : Sex)
    {i j : Fin Q.R} (hij : i ≠ j) (hi : mv Q s i x) (hj : mv Q s j x)
    (hri : Q.rank s (Q.person s x) i = 2) (hrj : Q.rank s (Q.person s x) j = 3) :
    ((Q.s i : ℝ) - 4) * h 2 + ((Q.s j : ℝ) - 4) * h 3 ≤ Q.Ex h s x := by
  unfold Member.Ex
  have := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun i => ((Q.s i : ℝ) - 4) * h (Q.rank s (Q.person s x) i))
    (s := {i, j}) (t := (Q.chainOf s (Q.person s x)).filter
      (fun i => 2 ≤ Q.rank s (Q.person s x) i ∧ Q.rank s (Q.person s x) i ≤ 3)) (by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      simp only [Finset.mem_filter]
      rcases hk with rfl | rfl
      · exact ⟨(mem_chainOf Q s _ _).mpr hi, by omega, by omega⟩
      · exact ⟨(mem_chainOf Q s _ _).mpr hj, by omega, by omega⟩)
    (fun k hk _ => Ex_term_nonneg Q h hh hx s k hk)
  rw [Finset.sum_pair hij] at this
  simp only [hri, hrj] at this
  exact this

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

theorem pLoss_ge_zx (hh : IsAdmissible h) {s : Sex} {G : Fin Q.R} {z x : Fin n}
    (hzG : Q.IsFirst z G) (hxz : x ≠ z) (hd : Q.dL s x = 2) {j : Fin Q.R}
    (hj : Q.le j G) (hxj : mv Q s j x) : h 2 + h (Q.dL s z) ≤ Q.pLoss h s G := by
  have hnn : ∀ r, 1 ≤ r → 0 ≤ h r := fun r hr => (hpos hh hr).le
  obtain ⟨ez, -⟩ := tm_one Q h s G z (down_chain_single Q hzG)
  have hc1 : 1 ≤ (Q.down G ∩ Q.chainOf s (Q.person s x)).card :=
    Finset.card_pos.mpr ⟨j, Finset.mem_inter.mpr ⟨(mem_down' Q G j).mpr hj,
      (mem_chainOf Q s _ j).mpr hxj⟩⟩
  have hc2 := card_le_dL Q s G x
  have ex : h 2 ≤ tm Q h s G x := by
    have p1 := hpos hh (le_refl 1)
    rcases (show (Q.down G ∩ Q.chainOf s (Q.person s x)).card = 1 ∨
        (Q.down G ∩ Q.chainOf s (Q.person s x)).card = 2 by omega) with e | e
    · obtain ⟨e1, -⟩ := tm_one Q h s G x e; rw [e1, hd]
    · obtain ⟨e1, -⟩ := tm_two Q h s G x e; rw [e1, hd]; norm_num; linarith
  have := pLoss_ge2 Q h hnn s G x z hxz
  rw [ez] at this
  linarith

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

theorem Tz_ge_d1 (hh : IsAdmissible h) {s : Sex} {G : Fin Q.R} {z : Fin n} (hzG : Q.IsFirst z G)
    (hfg : Q.firstGroup G = {z}) (hord : Q.IsOrdinary G) (h4 : 4 ≤ Q.s G)
    (hd1 : Q.dL s z = 1) : h 2 ≤ Q.Tz h s z := by
  rw [Tz_eq Q h hzG hfg hord]
  obtain ⟨hp, -⟩ := pLoss_ge_z Q h hh (s := s) hzG
  rw [hd1] at hp ⊢
  have := delta_d1 hh hp
  have := Finset.sum_nonneg (T2_term_nonneg Q h hzG h4 hh (s := s))
  linarith

theorem Tz_ge_F (hh : IsAdmissible h) {s : Sex} {G : Fin Q.R} {z : Fin n} (hzG : Q.IsFirst z G)
    (hfg : Q.firstGroup G = {z}) (hord : Q.IsOrdinary G) (h4 : 4 ≤ Q.s G) {F : Fin Q.R}
    (hzF : mv Q s F z) (hGF : G < F) (hgap : ∀ k, G < k → k < F → ¬ mv Q s k z)
    (h5 : 5 ≤ Q.s F) : h 2 ≤ Q.Tz h s z := by
  rw [Tz_eq Q h hzG hfg hord]
  obtain ⟨hp, hd⟩ := pLoss_ge_z Q h hh (s := s) hzG
  have := delta_nonneg hh hd hp
  have hr : Q.rank s (Q.person s z) F = 2 := by
    rw [rank_next Q s (isFirst_mv Q s hzG).1 hzF hGF hgap, rank_first Q s hzG]
  have hF := Finset.single_le_sum (f := fun i => h 2 * ((Q.s i : ℝ) - 4))
    (T2_term_nonneg Q h hzG h4 hh (s := s))
    (show F ∈ (Q.chainOf s (Q.person s z)).filter (fun i => Q.rank s (Q.person s z) i = 2) by
      simp only [Finset.mem_filter]; exact ⟨(mem_chainOf Q s _ F).mpr hzF, hr⟩)
  have h5' : (5 : ℝ) ≤ Q.s F := by exact_mod_cast h5
  have p2 := hpos hh (show 1 ≤ 2 by norm_num)
  nlinarith

theorem Tz_gt (hh : IsAdmissible h) {s : Sex} {G : Fin Q.R} {z : Fin n} (hzG : Q.IsFirst z G)
    (hfg : Q.firstGroup G = {z}) (hord : Q.IsOrdinary G) (h4 : 4 ≤ Q.s G)
    (hp : h 2 + h (Q.dL s z) ≤ Q.pLoss h s G) : 2 * h 2 < Q.Tz h s z := by
  rw [Tz_eq Q h hzG hfg hord]
  obtain ⟨-, hd⟩ := pLoss_ge_z Q h hh (s := s) hzG
  have := delta_ii hh hd hp
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

theorem next_step {s : Sex} {a : Fin Q.R} {ℓ : Fin n} (hex : ∃ k, a < k ∧ mv Q s k ℓ) :
    ∃ b, mv Q s b ℓ ∧ a < b ∧ ∀ k, a < k → k < b → ¬ mv Q s k ℓ := by
  classical
  have hne : (Finset.univ.filter fun j => mv Q s j ℓ ∧ a < j).Nonempty := by
    obtain ⟨k, h1, h2⟩ := hex; exact ⟨k, by simp [h1, h2]⟩
  set b := (Finset.univ.filter fun j => mv Q s j ℓ ∧ a < j).min' hne
  have hb : b ∈ Finset.univ.filter fun j => mv Q s j ℓ ∧ a < j := Finset.min'_mem _ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  refine ⟨b, hb.1, hb.2, fun k h1 h2 hk => ?_⟩
  have : b ≤ k := Finset.min'_le _ _ (by simp [hk, h1])
  exact absurd h2 (not_lt.mpr this)

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

theorem ord_of_big {G : Fin Q.R} {z : Fin n} (hzG : Q.IsFirst z G) (h5 : 5 ≤ Q.s G) :
    Q.IsOrdinary G := by
  refine ⟨⟨z, (mem_fg Q).mpr hzG⟩, fun hI => ?_, fun he => ?_⟩
  · have := init_s2 Q hI; omega
  · have := he.2; omega

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

theorem RA_ge_T (hh : IsAdmissible h) {A : Fin Q.R} (hAI : Q.IsInitialSwap A)
    (hP0 : ∀ i, Q.IsOrdinary i → Q.HasTripleIn A (Q.support i) → Q.s i < 5) (s : Sex)
    {S : Finset (Fin n)} (hS : S ⊆ Q.ZA A) :
    ∑ z ∈ S, Q.Tz h s z ≤ Q.RA h s A := by
  unfold Member.RA
  have e := Finset.sum_nonneg fun x hx => Ex_nonneg Q h hh (A := A) hx s
  have t := Finset.sum_le_sum_of_subset_of_nonneg hS
    (fun z hz _ => Tz_nonneg' Q h hh hAI hP0 s hz)
  linarith

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

theorem two_assoc {A : Fin Q.R} {u v : Fin n} (huv : u ≠ v) (hp : Q.participants A = {u, v})
    {x y : Fin n} (hx : x ∈ Q.XA A) (hy : y ∈ Q.XA A) (hxy : x ≠ y) :
    ∃ x1 x2 B1 B2, Assoc Q A x1 u v B1 ∧ Assoc Q A x2 v u B2 := by
  obtain ⟨a, b, B, hs⟩ := assoc_of_XA Q A x hx
  obtain ⟨a', b', B', hs'⟩ := assoc_of_XA Q A y hy
  rcases pair_cases huv hs.2.2.2.1 (hp.symm.trans hs.2.2.2.2.2.2.1) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases pair_cases huv hs'.2.2.2.1 (hp.symm.trans hs'.2.2.2.2.2.2.1) with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rw [h1, h2] at hs; rw [h3, h4] at hs'; exact absurd (assoc_unique_x Q hs hs') hxy
  · rw [h1, h2] at hs; rw [h3, h4] at hs'; exact ⟨x, y, B, B', hs, hs'⟩
  · rw [h1, h2] at hs; rw [h3, h4] at hs'; exact ⟨y, x, B', B, hs', hs⟩
  · rw [h1, h2] at hs; rw [h3, h4] at hs'; exact absurd (assoc_unique_x Q hs hs') hxy

end main

section cases
variable (Q : Member n) (h : ℕ → ℝ)

theorem mem_ZA {A G : Fin Q.R} {z : Fin n} (hzG : Q.IsFirst z G) (hord : Q.IsOrdinary G)
    (htr : Q.HasTripleIn A (Q.support G)) : z ∈ Q.ZA A := by
  simp only [Member.ZA, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨G, hzG, hord, htr⟩

/-- a fifth label in a third support of Case 1 gives a term `T_z ≥ b` -/
theorem case1z (hh : IsAdmissible h) {s : Sex} {A B E C : Fin Q.R} {x y p q : Fin n}
    (hP0 : ∀ i, Q.IsOrdinary i → Q.HasTripleIn A (Q.support i) → Q.s i < 5)
    (hAS : AS Q s A x p q B) (h' : AS Q s A y q p E) (hxX : x ∈ Q.XA A) (hyX : y ∈ Q.XA A)
    (hxC : mv Q s C x) (hBC : B < C) (hgapx : ∀ k, B < k → k < C → ¬ mv Q s k x)
    (hyC : mv Q s C y) (hEC : E < C) (hgapy : ∀ k, E < k → k < C → ¬ mv Q s k y)
    (hK : Q.support C = {p, q, x, y}) {τ : Fin Q.R} (hKτ : Q.support C ⊆ Q.support τ)
    {w : Fin n} (hwK : w ∉ Q.support C) (hwτ : w ∈ Q.support τ) (h5 : Q.s τ ≤ 5) :
    ∃ z ∈ Q.ZA A, h 2 ≤ Q.Tz h s z := by
  have hpq := hAS.pq; have hpx := hAS.px; have hqx := hAS.qx
  have hyp : y ≠ p := h'.qx.symm
  have hyq : y ≠ q := h'.px.symm
  have hxy : x ≠ y := by
    intro e
    have hBE : B = E := isFirst_unique Q hAS.fx (by rw [e]; exact h'.fx)
    rcases (hAS.mB q).mp (by rw [hBE]; exact h'.mvB1) with e2 | e2
    · exact hAS.pq e2.symm
    · exact hAS.qx e2
  have hc4 : (Q.support C).card = 4 := by
    rw [hK, card4 hpq hpx hyp.symm hqx hyq.symm hxy]
  have hτ : Q.support τ = insert w (Q.support C) := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.insert_subset hwτ hKτ)
    rw [Finset.card_insert_of_notMem hwK, hc4]
    unfold Member.s at h5; omega
  obtain ⟨j, hj, hmj⟩ := (support_iff Q s τ w).mp hwτ
  obtain ⟨G, hwG, hGj⟩ := exists_first Q s hmj
  have hGτ : Q.le G τ := le_tr Q ((chain_le_iff Q s (isFirst_mv Q s hwG).1 hmj).mpr hGj) hj
  have hGsub : Q.support G ⊆ insert w (Q.support C) := hτ ▸ support_mono Q hGτ
  obtain ⟨fg, ord, tr, nxt⟩ := zlemma Q hAS h' hxX hyX hxC hBC hgapx hyC hEC hgapy hK hP0 hwG hwK
    hGsub
  have hne : ¬ Q.IsExceptional w := by
    rintro ⟨i, hi, he⟩
    rw [isFirst_unique Q hi hwG] at he
    exact ord.2.2 he
  have h4 := (single_ord Q fg hne).2
  refine ⟨w, mem_ZA Q hwG ord tr, ?_⟩
  obtain ⟨-, hd⟩ := pLoss_ge_z Q h hh (s := s) hwG
  rcases (show Q.dL s w = 1 ∨ 2 ≤ Q.dL s w by omega) with e | e
  · exact Tz_ge_d1 Q h hh hwG fg ord h4 e
  · obtain ⟨F, hF, hGF, hgapF⟩ := exists_rank Q s (isFirst_mv Q s hwG).1
      (by rw [rank_first Q s hwG]; omega)
    exact Tz_ge_F Q h hh hwG fg ord h4 hF hGF hgapF (nxt F hF hGF hgapF)

/-- Case 1 of Lemma 8.3 -/
theorem case1 (hh : IsAdmissible h) {s : Sex} {A : Fin Q.R} {u v : Fin n}
    (hAI : Q.IsInitialSwap A) (huv : u ≠ v) (hp : Q.participants A = {u, v})
    (hu : Q.IsFirst u A) (hv : Q.IsFirst v A) (hD : 0 < Q.DStar h A)
    (hP0 : ∀ i, Q.IsOrdinary i → Q.HasTripleIn A (Q.support i) → Q.s i < 5)
    {B E C : Fin Q.R} {x y p q : Fin n}
    (hAS : AS Q s A x p q B) (h' : AS Q s A y q p E) (hxX : x ∈ Q.XA A) (hyX : y ∈ Q.XA A)
    (hxC : mv Q s C x) (hBC : B < C) (hgapx : ∀ k, B < k → k < C → ¬ mv Q s k x)
    (hyC : mv Q s C y) (hEC : E < C) (hgapy : ∀ k, E < k → k < C → ¬ mv Q s k y)
    (hK : Q.support C = {p, q, x, y}) (hxv : pm Q s C.succ x = p) (hyv : pm Q s C.succ y = q) :
    2 * h 2 ≤ Q.RA h s A := by
  have hpq := hAS.pq; have hpx := hAS.px; have hqx := hAS.qx
  have hyp : y ≠ p := h'.qx.symm
  have hyq : y ≠ q := h'.px.symm
  have hxy : x ≠ y := fun e => hpq (hxv.symm.trans (e ▸ hyv))
  obtain ⟨H41, H42, -⟩ := hh.2.2.2.2.2.1
  have p2 := hpos hh (show 1 ≤ 2 by norm_num)
  have p3 := hpos hh (show 1 ≤ 3 by norm_num)
  -- Lemma 7.2: no parent has degree three
  have no3 : ∀ ℓ, Q.IsFirst ℓ A → Q.dL (opp s) ℓ ≠ 3 := by
    intro ℓ hℓ e
    obtain ⟨x1, x2, B1, B2, hs1, hs2⟩ := two_assoc Q huv hp hxX hyX hxy
    have hℓuv : ℓ = u ∨ ℓ = v := by
      have : ℓ ∈ Q.firstGroup A := (mem_fg Q).mpr hℓ
      rw [fg_eq Q hp hu hv] at this; simpa using this
    have h3 : Q.dL .man u = 3 ∨ Q.dL .man v = 3 ∨ Q.dL .woman v = 3 ∨ Q.dL .woman u = 3 := by
      cases s <;> rcases hℓuv with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr e))
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
    have := lemma72 Q h hh hAI huv hp hu hv x1 B1 hs1 x2 B2 hs2 h3
    linarith
  have exx : ∃ k, C < k ∧ mv Q s k x := by
    by_contra hc
    push Not at hc
    exact no3 p hAS.fp (deg3 Q hAS h' hyC hEC hgapy hxv fun k hk hm => hc k hk hm)
  have exy : ∃ k, C < k ∧ mv Q s k y := by
    by_contra hc
    push Not at hc
    exact no3 q hAS.fq (deg3 Q h' hAS hxC hBC hgapx hyv fun k hk hm => hc k hk hm)
  obtain ⟨τx, hxτ, hCτx, hgτx⟩ := next_step Q exx
  obtain ⟨τy, hyτ, hCτy, hgτy⟩ := next_step Q exy
  have rCx : Q.rank s (Q.person s x) C = 2 := by
    rw [rank_next Q s hAS.mvB2 hxC hBC hgapx, rank_first Q s hAS.fx]
  have rCy : Q.rank s (Q.person s y) C = 2 := by
    rw [rank_next Q s h'.mvB2 hyC hEC hgapy, rank_first Q s h'.fx]
  have rτx : Q.rank s (Q.person s x) τx = 3 := by rw [rank_next Q s hxC hxτ hCτx hgτx, rCx]
  have rτy : Q.rank s (Q.person s y) τy = 3 := by rw [rank_next Q s hyC hyτ hCτy hgτy, rCy]
  obtain ⟨wx, a1, a2, a3, a4, wxS⟩ := third Q hAS h' hxC hEC hxv hxτ hCτx hgτx
  obtain ⟨wy, b1, b2, b3, b4, wyS⟩ := third Q h' hAS hyC hBC hyv hyτ hCτy hgτy
  have sC : Q.s C = 4 := by unfold Member.s; rw [hK, card4 hpq hpx hyp.symm hqx hyq.symm hxy]
  have wxK : wx ∉ Q.support C := by rw [hK]; simp [a1, a2, a3, a4]
  have wyK : wy ∉ Q.support C := by rw [hK]; simp [b1, b2, b3, b4]
  have Kx : Q.support C ⊆ Q.support τx := support_mono Q (chain_le Q s hxC hxτ hCτx)
  have Ky : Q.support C ⊆ Q.support τy := support_mono Q (chain_le Q s hyC hyτ hCτy)
  have s5x : 5 ≤ Q.s τx := by
    have := Finset.card_le_card (Finset.insert_subset wxS Kx)
    rw [Finset.card_insert_of_notMem wxK] at this
    unfold Member.s; unfold Member.s at sC; omega
  have s5y : 5 ≤ Q.s τy := by
    have := Finset.card_le_card (Finset.insert_subset wyS Ky)
    rw [Finset.card_insert_of_notMem wyK] at this
    unfold Member.s; unfold Member.s at sC; omega
  have Ex1 := Ex_ge2 Q h hh hxX s (Fin.ne_of_lt hCτx) hxC hxτ rCx rτx
  have Ey1 := Ex_ge2 Q h hh hyX s (Fin.ne_of_lt hCτy) hyC hyτ rCy rτy
  rw [sC] at Ex1 Ey1
  push_cast at Ex1 Ey1
  simp only [sub_self, zero_mul, zero_add] at Ex1 Ey1
  have r5x : (5 : ℝ) ≤ Q.s τx := by exact_mod_cast s5x
  have r5y : (5 : ℝ) ≤ Q.s τy := by exact_mod_cast s5y
  have hXsub : ({x, y} : Finset (Fin n)) ⊆ Q.XA A := by
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hxX
    · exact hyX
  by_cases big : 6 ≤ Q.s τx ∧ 6 ≤ Q.s τy
  · have r6x : (6 : ℝ) ≤ Q.s τx := by exact_mod_cast big.1
    have r6y : (6 : ℝ) ≤ Q.s τy := by exact_mod_cast big.2
    have := RA_ge Q h hh hAI hP0 s hXsub (Finset.empty_subset _)
    rw [Finset.sum_pair hxy, Finset.sum_empty] at this
    have k1 : 2 * h 3 ≤ ((Q.s τx : ℝ) - 4) * h 3 := by nlinarith
    have k2 : 2 * h 3 ≤ ((Q.s τy : ℝ) - 4) * h 3 := by nlinarith
    linarith
  · have hz : ∃ z ∈ Q.ZA A, h 2 ≤ Q.Tz h s z := by
      rcases not_and_or.mp big with b | b
      · exact case1z Q h hh hP0 hAS h' hxX hyX hxC hBC hgapx hyC hEC hgapy hK Kx wxK wxS
          (by omega)
      · have hK' : Q.support C = {q, p, y, x} := by
          rw [hK]; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
        exact case1z Q h hh hP0 h' hAS hyX hxX hyC hEC hgapy hxC hBC hgapx hK' Ky wyK wyS
          (by omega)
    obtain ⟨z, hzZ, hTz⟩ := hz
    have := RA_ge Q h hh hAI hP0 s hXsub (Finset.singleton_subset_iff.mpr hzZ)
    rw [Finset.sum_pair hxy, Finset.sum_singleton] at this
    have k1 : h 3 ≤ ((Q.s τx : ℝ) - 4) * h 3 := by nlinarith
    have k2 : h 3 ≤ ((Q.s τy : ℝ) - 4) * h 3 := by nlinarith
    linarith

end cases

section perx
variable (Q : Member n) (h : ℕ → ℝ)

/-- the bound obtained for one exceptional label of degree at least two -/
def Served (s : Sex) (A : Fin Q.R) (x : Fin n) : Prop :=
  h 2 ≤ Q.Ex h s x ∨
    ∃ y G, y ∈ Q.ZA A ∧ h 2 ≤ Q.Tz h s y ∧ Q.IsFirst y G ∧
      insert x (Q.firstGroup A) ⊆ Q.support G

theorem perx (hh : IsAdmissible h) {s : Sex} {A : Fin Q.R} {u v : Fin n}
    (hAI : Q.IsInitialSwap A) (huv : u ≠ v) (hp : Q.participants A = {u, v})
    (hu : Q.IsFirst u A) (hv : Q.IsFirst v A) (hD : 0 < Q.DStar h A)
    (hP0 : ∀ i, Q.IsOrdinary i → Q.HasTripleIn A (Q.support i) → Q.s i < 5)
    {x : Fin n} (hxX : x ∈ Q.XA A) (hd : 2 ≤ Q.dL s x) :
    Served Q h s A x ∨ 2 * h 2 ≤ Q.RA h s A := by
  classical
  obtain ⟨p, q, B, hAS⟩ := as_XA Q hxX s
  have hpq := hAS.pq; have hpx := hAS.px; have hqx := hAS.qx
  obtain ⟨H41, H42, -⟩ := hh.2.2.2.2.2.1
  have p2 := hpos hh (show 1 ≤ 2 by norm_num)
  have p3 := hpos hh (show 1 ≤ 3 by norm_num)
  obtain ⟨C, hxC, hBC, hgap⟩ := exists_rank Q s hAS.mvB2 (by rw [rank_first Q s hAS.fx]; omega)
  have rC : Q.rank s (Q.person s x) C = 2 := by
    rw [rank_next Q s hAS.mvB2 hxC hBC hgap, rank_first Q s hAS.fx]
  have s4 := P1 Q hAS hxC hBC
  by_cases h5 : 5 ≤ Q.s C
  · left; left
    have := Ex_ge Q h hh hxX s hxC (by omega) (by omega)
    rw [rC] at this
    have r5 : (5 : ℝ) ≤ Q.s C := by exact_mod_cast h5
    nlinarith
  have sC4 : Q.s C = 4 := by omega
  have sub3 := hAS.supB_le (mem_support_self Q s hxC)
  obtain ⟨y, hy⟩ : ∃ y, Q.support C \ {p, q, x} = {y} := by
    apply Finset.card_eq_one.mp
    rw [Finset.card_sdiff_of_subset sub3, hAS.card]
    unfold Member.s at sC4; omega
  have hyC : y ∈ Q.support C := (Finset.mem_sdiff.mp (hy ▸ Finset.mem_singleton_self y)).1
  have hyn : y ∉ ({p, q, x} : Finset (Fin n)) :=
    (Finset.mem_sdiff.mp (hy ▸ Finset.mem_singleton_self y)).2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyn
  obtain ⟨hyp, hyq, hyx⟩ := hyn
  replace hyp : y ≠ p := hyp
  replace hyq : y ≠ q := hyq
  replace hyx : y ≠ x := hyx
  have hK : Q.support C = {p, q, x, y} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      rcases mem4 hw with e | e | e | e <;> rw [e]
      · exact sub3 (by simp)
      · exact sub3 (by simp)
      · exact sub3 (by simp)
      · exact hyC
    · rw [card4 hpq hpx hyp.symm hqx hyq.symm hyx.symm]; unfold Member.s at sC4; omega
  obtain ⟨j, hj, hmj⟩ := (support_iff Q s C y).mp hyC
  obtain ⟨γ, hyγ, -⟩ := exists_first Q s hmj
  have fgA' := fgA Q hAS
  by_cases hex : Q.IsExceptional y
  · right
    obtain ⟨E, h', hyX, hEC, hyCm, hgapy, hxv, hyv⟩ := P3 Q hAS hxC hBC hgap hK hyp hyq hyx hex
    exact case1 Q h hh hAI huv hp hu hv hD hP0 hAS h' hxX hyX hxC hBC hgap hyCm hEC hgapy hK hxv hyv
  obtain ⟨fgγ, ordγ, Sγ⟩ := case2_y Q hAS hK hyp hyq hyx hyγ hex
  have trγ : Q.HasTripleIn A (Q.support γ) := triple Q hAS hxX (by rw [Sγ]; exact sub3)
  have yZ := mem_ZA Q hyγ ordγ trγ
  have h4γ : 4 ≤ Q.s γ := by unfold Member.s; rw [Sγ]; unfold Member.s at sC4; omega
  have serve : h 2 ≤ Q.Tz h s y → Served Q h s A x := fun hT => Or.inr ⟨y, γ, yZ, hT, hyγ, by
    rw [fgA', Sγ, hK]; intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢; tauto⟩
  by_cases hγC : γ = C
  · left
    apply serve
    obtain ⟨-, hdy⟩ := pLoss_ge_z Q h hh (s := s) hyγ
    rcases (show Q.dL s y = 1 ∨ 2 ≤ Q.dL s y by omega) with e | e
    · exact Tz_ge_d1 Q h hh hyγ fgγ ordγ h4γ e
    · obtain ⟨F, hF, hγF, hgapF⟩ := exists_rank Q s (isFirst_mv Q s hyγ).1
        (by rw [rank_first Q s hyγ]; omega)
      have hyCm : mv Q s C y := hγC ▸ (isFirst_mv Q s hyγ).1
      rw [hγC] at hγF hgapF
      exact Tz_ge_F Q h hh hyγ fgγ ordγ h4γ hF (hγC ▸ hγF) (hγC ▸ hgapF)
        (P4 Q hAS hxC hBC hgap hK hyCm hF hγF hgapF)
  rcases (show Q.dL s x = 2 ∨ 3 ≤ Q.dL s x by omega) with e | e
  · right
    have hBγ : Q.le B γ := hAS.B_le (by rw [Sγ, hK]; simp)
    have hT := Tz_gt Q h hh hyγ fgγ ordγ h4γ
      (pLoss_ge_zx Q h hh hyγ hyx.symm e hBγ hAS.mvB2)
    have := RA_ge_T Q h hh hAI hP0 s (Finset.singleton_subset_iff.mpr yZ)
    rw [Finset.sum_singleton] at this
    linarith
  · left; left
    obtain ⟨τ, hxτ, hCτ, hgapτ⟩ := exists_rank Q s hxC (by rw [rC]; omega)
    have rτ : Q.rank s (Q.person s x) τ = 3 := by rw [rank_next Q s hxC hxτ hCτ hgapτ, rC]
    rcases P5 Q hAS hxC hBC hgap hK hyp hyq hyx hyγ hγC (Sγ) hxτ hCτ with h6 | ⟨G, z, hzG, hzK, hsub⟩
    · have := Ex_ge Q h hh hxX s hxτ (by omega) (by omega)
      rw [rτ] at this
      have r6 : (6 : ℝ) ≤ Q.s τ := by exact_mod_cast h6
      have : 2 * h 3 ≤ ((Q.s τ : ℝ) - 4) * h 3 := by nlinarith
      linarith
    · exfalso
      have h5G : 5 ≤ Q.s G := by
        have := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem hzK] at this
        unfold Member.s; unfold Member.s at sC4; omega
      have ord := ord_of_big Q hzG h5G
      have tr : Q.HasTripleIn A (Q.support G) :=
        triple Q hAS hxX (fun w hw => hsub (Finset.mem_insert_of_mem (sub3 hw)))
      have := hP0 G ord tr
      omega

end perx

section final83
variable (Q : Member n) (h : ℕ → ℝ)

theorem distinct_y {A : Fin Q.R} (hAI : Q.IsInitialSwap A)
    (hP0 : ∀ i, Q.IsOrdinary i → Q.HasTripleIn A (Q.support i) → Q.s i < 5)
    {x1 x2 y : Fin n} {G1 G2 : Fin Q.R} (hx1 : x1 ∈ Q.XA A) (hx2 : x2 ∈ Q.XA A) (h12 : x1 ≠ x2)
    (hy : y ∈ Q.ZA A) (hG1 : Q.IsFirst y G1) (hG2 : Q.IsFirst y G2)
    (hs1 : insert x1 (Q.firstGroup A) ⊆ Q.support G1)
    (hs2 : insert x2 (Q.firstGroup A) ⊆ Q.support G2) : False := by
  obtain ⟨G, hyG, hord, -, -, htr⟩ := ZA_spec Q hAI hP0 hy
  rw [isFirst_unique Q hG1 hyG] at hs1
  rw [isFirst_unique Q hG2 hyG] at hs2
  have h5 := hP0 G hord htr
  obtain ⟨p, q, B1, a1⟩ := as_XA Q hx1 .man
  obtain ⟨p', q', B2, a2⟩ := as_XA Q hx2 .man
  rw [fgA Q a1] at hs1 hs2
  have hGA : G ≠ A := fun e => hord.2.1 (e ▸ hAI)
  have hGB1 : G ≠ B1 := fun e => hord.2.2 (e ▸ exc_B Q a1 hx1)
  have hGB2 : G ≠ B2 := fun e => hord.2.2 (e ▸ exc_B Q a2 hx2)
  have hyp : y ≠ p := fun e => hGA (isFirst_unique Q hyG (e ▸ a1.fp))
  have hyq : y ≠ q := fun e => hGA (isFirst_unique Q hyG (e ▸ a1.fq))
  have hy1 : y ≠ x1 := fun e => hGB1 (isFirst_unique Q hyG (e ▸ a1.fx))
  have hy2 : y ≠ x2 := fun e => hGB2 (isFirst_unique Q hyG (e ▸ a2.fx))
  have hx1p : x1 ≠ p := a1.px.symm
  have hx1q : x1 ≠ q := a1.qx.symm
  have hx2p : x2 ≠ p := fun e => by
    have := isFirst_unique Q a2.fx (e ▸ a1.fp); exact absurd this (Fin.ne_of_lt a2.lt).symm
  have hx2q : x2 ≠ q := fun e => by
    have := isFirst_unique Q a2.fx (e ▸ a1.fq); exact absurd this (Fin.ne_of_lt a2.lt).symm
  have sub : ({p, q, x1, x2, y} : Finset (Fin n)) ⊆ Q.support G := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with e | e | e | e | e <;> rw [e]
    · exact hs1 (by simp)
    · exact hs1 (by simp)
    · exact hs1 (by simp)
    · exact hs2 (by simp)
    · exact mem_support_self Q .man (isFirst_mv Q .man hyG).1
  have := Finset.card_le_card sub
  rw [card5 a1.pq hx1p.symm hx2p.symm hyp.symm hx1q.symm hx2q.symm hyq.symm h12 hy1.symm
    hy2.symm] at this
  unfold Member.s at h5; omega

theorem main83 (hh : IsAdmissible h) {A : Fin Q.R} (hA : A ∈ Q.P0) (hD : 0 < Q.DStar h A)
    (s : Sex) : h 2 * (Q.NA s A : ℝ) ≤ Q.RA h s A := by
  classical
  obtain ⟨hAI, hP0⟩ := P0_spec Q hA
  obtain ⟨u, v, huv, hp⟩ := Finset.card_eq_two.mp hAI.1
  have hu : Q.IsFirst u A := hAI.2 u (by rw [hp]; simp)
  have hv : Q.IsFirst v A := hAI.2 v (by rw [hp]; simp)
  have p2 := hpos hh (show 1 ≤ 2 by norm_num)
  have hXc := XA_card Q hp hu hv
  have hR0 : 0 ≤ Q.RA h s A := by
    have := RA_ge_T Q h hh hAI hP0 s (Finset.empty_subset (Q.ZA A))
    rwa [Finset.sum_empty] at this
  by_cases big : 2 * h 2 ≤ Q.RA h s A
  · have hNA : Q.NA s A ≤ 2 := le_trans (Finset.card_filter_le _ _) hXc
    have : (Q.NA s A : ℝ) ≤ 2 := by exact_mod_cast hNA
    nlinarith
  have serv : ∀ x ∈ Q.XA A, (if 2 ≤ Q.dL s x then h 2 else 0) ≤ Q.Ex h s x ∨
      ∃ y G, y ∈ Q.ZA A ∧ (if 2 ≤ Q.dL s x then h 2 else 0) ≤ Q.Tz h s y ∧ Q.IsFirst y G ∧
        insert x (Q.firstGroup A) ⊆ Q.support G := by
    intro x hx
    split_ifs with hd
    · rcases perx Q h hh hAI huv hp hu hv hD hP0 hx hd with hs | hb
      · rcases hs with hE | ⟨y, G, a, b, c, d⟩
        · exact Or.inl hE
        · exact Or.inr ⟨y, G, a, b, c, d⟩
      · exact absurd hb big
    · exact Or.inl (Ex_nonneg Q h hh hx s)
  rw [hN Q h A s]
  rcases (show (Q.XA A).card = 0 ∨ (Q.XA A).card = 1 ∨ (Q.XA A).card = 2 by omega) with c | c | c
  · rw [Finset.card_eq_zero.mp c, Finset.sum_empty]; exact hR0
  · obtain ⟨x, hX⟩ := Finset.card_eq_one.mp c
    have hx : x ∈ Q.XA A := by rw [hX]; simp
    rw [hX, Finset.sum_singleton]
    rcases serv x hx with hE | ⟨y, G, hy, hT, -, -⟩
    · have := RA_ge Q h hh hAI hP0 s (Finset.singleton_subset_iff.mpr hx)
        (Finset.empty_subset (Q.ZA A))
      rw [Finset.sum_singleton, Finset.sum_empty] at this
      linarith
    · have := RA_ge_T Q h hh hAI hP0 s (Finset.singleton_subset_iff.mpr hy)
      rw [Finset.sum_singleton] at this
      linarith
  · obtain ⟨x1, x2, h12, hX⟩ := Finset.card_eq_two.mp c
    have hx1 : x1 ∈ Q.XA A := by rw [hX]; simp
    have hx2 : x2 ∈ Q.XA A := by rw [hX]; simp
    have hXs : ({x1, x2} : Finset (Fin n)) ⊆ Q.XA A := by rw [hX]
    rw [hX, Finset.sum_pair h12]
    have e1 := Ex_nonneg Q h hh hx1 s
    have e2 := Ex_nonneg Q h hh hx2 s
    rcases serv x1 hx1 with a | ⟨y1, G1, hy1, hT1, hf1, hs1⟩ <;>
      rcases serv x2 hx2 with b | ⟨y2, G2, hy2, hT2, hf2, hs2⟩
    · have := RA_ge Q h hh hAI hP0 s hXs (Finset.empty_subset (Q.ZA A))
      rw [Finset.sum_pair h12, Finset.sum_empty] at this
      linarith
    · have := RA_ge Q h hh hAI hP0 s hXs (Finset.singleton_subset_iff.mpr hy2)
      rw [Finset.sum_pair h12, Finset.sum_singleton] at this
      linarith
    · have := RA_ge Q h hh hAI hP0 s hXs (Finset.singleton_subset_iff.mpr hy1)
      rw [Finset.sum_pair h12, Finset.sum_singleton] at this
      linarith
    · have hy12 : y1 ≠ y2 := by
        intro e
        rw [← e] at hf2
        exact distinct_y Q hAI hP0 hx1 hx2 h12 hy1 hf1 hf2 hs1 hs2
      have hS : ({y1, y2} : Finset (Fin n)) ⊆ Q.ZA A := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hy1
        · exact hy2
      have := RA_ge Q h hh hAI hP0 s hXs hS
      rw [Finset.sum_pair h12, Finset.sum_pair hy12] at this
      linarith

end final83

end Dev.L83

theorem chk_lemma_8_3 {n : ℕ} (h : ℕ → ℝ) (hh : IsAdmissible h) (Q : Member n) (A : Fin Q.R)
    (hA : A ∈ Q.P0) (hD : 0 < Q.DStar h A) (s : Sex) :
    h 2 * (Q.NA s A : ℝ) ≤ Q.RA h s A :=
  Dev.L83.main83 Q h hh hA hD s

end StableCount
end

theorem solution : type_of% @StableCount.chk_lemma_8_3 := @StableCount.chk_lemma_8_3
