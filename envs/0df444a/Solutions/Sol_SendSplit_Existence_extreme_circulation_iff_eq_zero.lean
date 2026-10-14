-- Prove2me | solution 1 for SendSplit.Existence.extreme_circulation_iff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:28:40.024586+00:00
-- url     : https://prove2.me/submissions/201cc2d6-4f04-43eb-b1be-d3a0a1bd4b1a

import Mathlib
import Definitions.Def_SendSplit_Existence_Network



namespace SendSplit.Existence
variable {n : ℕ}

lemma exists_first_repeat {β : Type*} [Finite β] (w : ℕ → β) :
    ∃ a L : ℕ, 0 < L ∧ (∀ i j, i < L → j < L → w (a + i) = w (a + j) → i = j) ∧ w (a + L) = w a := by
  classical
  obtain ⟨x, y, hxy, hw⟩ := Finite.exists_ne_map_eq_of_infinite w
  have hQ : ∃ b, ∃ a, a < b ∧ w a = w b := by
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨y, x, h, hw⟩
    · exact ⟨x, y, h, hw.symm⟩
  let b := Nat.find hQ
  obtain ⟨a, hab, hwab⟩ := Nat.find_spec hQ
  refine ⟨a, b - a, by omega, ?_, ?_⟩
  · intro i j hi hj hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : b ≤ a + j := Nat.find_min' hQ ⟨a + i, by omega, hij⟩
      omega
    · have : b ≤ a + i := Nat.find_min' hQ ⟨a + j, by omega, hij.symm⟩
      omega
  · have : a + (b - a) = b := by omega
    rw [this]; exact hwab.symm

theorem extreme_circ_core (G : ArcGraph n) (x : Fin n → Fin n → ℝ)
    (hx : IsCirculation G x) :
    IsExtremeFlow G (fun _ => 0) x ↔ x = 0 := by
  classical
  constructor
  · rintro ⟨_, hforest⟩
    by_contra hne
    obtain ⟨⟨hnn, hzero⟩, hcons⟩ := hx
    -- P j : j has an outgoing arc with positive flow
    let P : Fin n → Prop := fun j => ∃ k, (j, k) ∈ G.A ∧ 0 < x j k
    have hP : ∀ j, P j → ∃ k, (j, k) ∈ G.A ∧ 0 < x j k ∧ P k := by
      intro j ⟨k, hjk, hxk⟩
      refine ⟨k, hjk, hxk, ?_⟩
      have h1 := hcons k
      have hin : x j k ≤ ∑ j' ∈ Finset.univ.filter (fun j' => (j', k) ∈ G.A), x j' k :=
        Finset.single_le_sum (f := fun j' => x j' k) (fun j' _ => hnn j' k) (by simp [hjk])
      by_contra hno
      have : ∑ k' ∈ Finset.univ.filter (fun k' => (k, k') ∈ G.A), x k k' ≤ 0 := by
        refine Finset.sum_nonpos fun k' hk' => ?_
        by_contra hpos
        exact hno ⟨k', (Finset.mem_filter.1 hk').2, not_le.1 hpos⟩
      simp only at h1
      linarith
    let nxt : Fin n → Fin n := fun j => if h : P j then Classical.choose (hP j h) else j
    have hnxt : ∀ j, P j → (j, nxt j) ∈ G.A ∧ 0 < x j (nxt j) ∧ P (nxt j) := by
      intro j hj
      simp only [nxt, dif_pos hj]
      exact Classical.choose_spec (hP j hj)
    obtain ⟨i, j, hij⟩ : ∃ i j, x i j ≠ 0 := by
      by_contra h; push_neg at h; exact hne (funext fun i => funext fun j => h i j)
    have hijA : (i, j) ∈ G.A := by
      by_contra h; exact hij (hzero i j h)
    have hs : P i := ⟨j, hijA, lt_of_le_of_ne (hnn i j) (Ne.symm hij)⟩
    let w : ℕ → Fin n := fun k => nxt^[k] i
    have hwP : ∀ k, P (w k) := by
      intro k; induction k with
      | zero => exact hs
      | succ k ih =>
        have : w (k+1) = nxt (w k) := Function.iterate_succ_apply' nxt k i
        rw [this]; exact (hnxt _ ih).2.2
    have hwA : ∀ k, (w k, w (k+1)) ∈ G.A ∧ 0 < x (w k) (w (k+1)) := by
      intro k
      have : w (k+1) = nxt (w k) := Function.iterate_succ_apply' nxt k i
      rw [this]; exact ⟨(hnxt _ (hwP k)).1, (hnxt _ (hwP k)).2.1⟩
    obtain ⟨a, L, hL, hinj, hrep⟩ := exists_first_repeat w
    have hL2 : 2 ≤ L := by
      by_contra h
      have : L = 1 := by omega
      subst this
      have h1 := (hwA a).1
      have : w (a + 1) = w a := hrep
      rw [this] at h1
      exact G.loopless _ h1 rfl
    obtain ⟨m, rfl⟩ : ∃ m, L = m + 2 := ⟨L - 2, by omega⟩
    apply hforest
    refine ⟨m, fun k => w (a + k.val), fun k => (w (a + k.val), w (a + (k + 1).val)), ?_, ?_, ?_⟩
    · intro k k' h
      exact Fin.ext (hinj _ _ k.2 k'.2 h)
    · intro k k' h
      have := (Prod.mk.inj h).1
      exact Fin.ext (hinj _ _ k.2 k'.2 this)
    · intro k
      have hnext : w (a + (k + 1).val) = w (a + k.val + 1) := by
        rw [Fin.val_add_one]
        split_ifs with hlast
        · have hk : k.val = m + 1 := by
            have := congrArg Fin.val hlast
            simp at this; omega
          simp only [Fin.val_zero, add_zero]
          rw [hk]
          have : a + (m + 1) + 1 = a + (m + 2) := by ring
          rw [this, hrep]
        · rfl
      refine ⟨?_, Or.inl ?_⟩
      · simp only [support, Finset.mem_filter]
        rw [hnext]
        exact ⟨(hwA _).1, (hwA _).2.ne'⟩
      · simp only [hnext]
  · intro h
    subst h
    refine ⟨hx, ?_⟩
    rintro ⟨m, v, e, _, _, hk⟩
    have := (hk 0).1
    simp [support] at this

end SendSplit.Existence

open SendSplit.Existence


theorem solution {n : ℕ} (G : ArcGraph n) (x : Fin n → Fin n → ℝ)
    (hx : IsCirculation G x) :
    IsExtremeFlow G (fun _ => 0) x ↔ x = 0 := by
  exact extreme_circ_core G x hx
