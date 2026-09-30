-- Prove2me | solution 1 for SupplyChainTheory.comb_inequality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T20:30:56.903194+00:00
-- url     : https://prove2.me/submissions/5dabf357-1236-4bab-a89f-765b3af5bc03

import Mathlib
import Definitions.Def_SupplyChainTheory_tsp

open Classical SupplyChainTheory

/-! ### Counting tour edges by position (on `Fin (m + 1)`, so that `k + 1` makes sense) -/

/-- The successor position on a tour. -/
private lemma rot_eq {m : ℕ} (k : Fin (m + 1)) : finRotate (m + 1) k = k + 1 := finRotate_apply k

/-- For at least three nodes, distinct positions give distinct tour edges. -/
private lemma tourEdge_injective {m : ℕ} (hm : 2 ≤ m) (τ : Equiv.Perm (Fin (m + 1))) :
    Function.Injective (fun k : Fin (m + 1) => s(τ k, τ (finRotate (m + 1) k))) := by
  intro a b h
  simp only [Sym2.eq_iff] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact τ.injective h1
  · have e1 := τ.injective h1
    have e2 := τ.injective h2
    rw [rot_eq] at e1 e2
    -- `a = b + 1` and `a + 1 = b` force `1 + 1 = 0` in `Fin (m + 1)`, impossible for `m ≥ 2`.
    exfalso
    have h3 : b + (1 + 1) = b + 0 := by rw [add_zero, ← add_assoc, ← e1, e2]
    have h4 : ((1 + 1 : Fin (m + 1)) : ℕ) = 0 := by
      rw [add_left_cancel h3]; rfl
    rw [Fin.val_add, Fin.val_one', Nat.one_mod_eq_one.mpr (by omega),
      Nat.mod_eq_of_lt (by omega)] at h4
    omega

/-- Counting tour edges with a property is counting positions with that property. -/
private lemma card_tourEdges_filter {m : ℕ} (hm : 2 ≤ m) (τ : Equiv.Perm (Fin (m + 1)))
    (P : Sym2 (Fin (m + 1)) → Prop) [DecidablePred P] :
    ((tourEdges τ).filter P).card
      = (Finset.univ.filter (fun k => P s(τ k, τ (finRotate (m + 1) k)))).card := by
  rw [tourEdges, Finset.filter_image, Finset.card_image_of_injective _ (tourEdge_injective hm τ)]

private lemma edgesWithin_eq {m : ℕ} (hm : 2 ≤ m) (τ : Equiv.Perm (Fin (m + 1)))
    (S : Finset (Fin (m + 1))) :
    edgesWithin τ S
      = (Finset.univ.filter (fun k => τ k ∈ S ∧ τ (finRotate (m + 1) k) ∈ S)).card := by
  rw [edgesWithin, card_tourEdges_filter hm]
  congr 1; ext k; simp

private lemma edgesLeaving_eq {m : ℕ} (hm : 2 ≤ m) (τ : Equiv.Perm (Fin (m + 1)))
    (S : Finset (Fin (m + 1))) :
    edgesLeaving τ S
      = (Finset.univ.filter (fun k => (τ k ∈ S ↔ τ (finRotate (m + 1) k) ∉ S))).card := by
  rw [edgesLeaving, card_tourEdges_filter hm]
  congr 1; ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff]
  constructor
  · rintro ⟨v, hv, hvS, w, hw, hwS⟩
    rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;> tauto
  · intro h
    by_cases ha : τ k ∈ S
    · exact ⟨τ k, Or.inl rfl, ha, τ (finRotate (m + 1) k), Or.inr rfl, h.mp ha⟩
    · have hb : τ (finRotate (m + 1) k) ∈ S := by by_contra hb; exact ha (h.mpr hb)
      exact ⟨τ (finRotate (m + 1) k), Or.inr rfl, hb, τ k, Or.inl rfl, ha⟩

/-- Degree equation of a tour: every node has tour degree `2`, so
`2 x(E(S)) + x(δ(S)) = 2|S|`. -/
private lemma degree_identity {m : ℕ} (hm : 2 ≤ m) (τ : Equiv.Perm (Fin (m + 1)))
    (S : Finset (Fin (m + 1))) : 2 * edgesWithin τ S + edgesLeaving τ S = 2 * S.card := by
  rw [edgesWithin_eq hm, edgesLeaving_eq hm]
  simp only [Finset.card_filter]
  have hperm : ∀ σ : Equiv.Perm (Fin (m + 1)), ∑ k, (if σ k ∈ S then 1 else 0) = S.card := by
    intro σ
    rw [Equiv.sum_comp σ (fun v => if v ∈ S then 1 else 0), ← Finset.card_filter]
    congr 1; ext v; simp
  have hA := hperm τ
  have hB : ∑ k, (if τ (finRotate (m + 1) k) ∈ S then 1 else 0) = S.card :=
    hperm (τ * finRotate (m + 1))
  calc 2 * (∑ k, if τ k ∈ S ∧ τ (finRotate (m + 1) k) ∈ S then 1 else 0)
        + ∑ k, (if (τ k ∈ S ↔ τ (finRotate (m + 1) k) ∉ S) then 1 else 0)
      = ∑ k, ((if τ k ∈ S then 1 else 0) + if τ (finRotate (m + 1) k) ∈ S then 1 else 0) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        split_ifs <;> simp_all
    _ = 2 * S.card := by rw [Finset.sum_add_distrib, hA, hB]; ring

/-- A tour leaves every nonempty proper node set. -/
private lemma exists_leaving {m : ℕ} (τ : Equiv.Perm (Fin (m + 1))) (S : Finset (Fin (m + 1)))
    (hS : S.Nonempty) (hS' : S ≠ Finset.univ) :
    ∃ k, τ k ∈ S ∧ τ (finRotate (m + 1) k) ∉ S := by
  by_contra hno
  push Not at hno
  obtain ⟨v, hv⟩ := hS
  -- Walking along the tour from `v` never leaves `S`, so `S` contains every node.
  have hall : ∀ j : ℕ, τ ((finRotate (m + 1) ^ j) (τ.symm v)) ∈ S := by
    intro j
    induction j with
    | zero => simpa using hv
    | succ j ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hno _ ih
  apply hS'
  ext w
  simp only [Finset.mem_univ, iff_true]
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    have hwv : w = v := Fin.ext (by have := w.isLt; have := v.isLt; omega)
    rw [hwv]; exact hv
  -- `finRotate` is a single cycle through every position.
  have hsupp : ∀ k : Fin (m + 1), finRotate (m + 1) k ≠ k := by
    intro k
    rw [← Equiv.Perm.mem_support, support_finRotate_of_le (by omega)]
    exact Finset.mem_univ k
  obtain ⟨j, hj⟩ := (isCycle_finRotate_of_le (by omega)).exists_pow_eq
    (hsupp (τ.symm v)) (hsupp (τ.symm w))
  have := hall j
  rw [hj] at this
  simpa using this

/-- Subtour elimination: a tour has at most `|S| - 1` edges inside a nonempty proper set. -/
private lemma subtour {m : ℕ} (hm : 2 ≤ m) (τ : Equiv.Perm (Fin (m + 1)))
    (S : Finset (Fin (m + 1))) (hS : S.Nonempty) (hS' : S ≠ Finset.univ) :
    edgesWithin τ S + 1 ≤ S.card := by
  have hid := degree_identity hm τ S
  have hl : 1 ≤ edgesLeaving τ S := by
    obtain ⟨k, hk1, hk2⟩ := exists_leaving τ S hS hS'
    rw [edgesLeaving_eq hm]
    exact Finset.card_pos.mpr ⟨k, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact iff_of_true hk1 hk2⟩
  omega

theorem solution {n s : ℕ} (hn : 3 ≤ n) (τ : Equiv.Perm (Fin n))
    (H : Finset (Fin n)) (T : Fin s → Finset (Fin n)) (hcomb : IsComb H T) :
    edgesWithin τ H + ∑ k, edgesWithin τ (T k) + (s + 1) / 2
      ≤ H.card + ∑ k, ((T k).card - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  obtain ⟨hmeet, hdisj, hs3, hsodd⟩ := hcomb
  -- The part of tooth `j` inside the handle, the part outside, and the tour edges of `T j`
  -- joining the two parts (these cross the handle).
  set P : Fin s → Finset (Fin (m + 1)) := fun j => (T j).filter (· ∈ H) with hP
  set Q : Fin s → Finset (Fin (m + 1)) := fun j => (T j).filter (· ∉ H) with hQ
  set nx : Fin (m + 1) → Fin (m + 1) := fun k => τ (finRotate (m + 1) k) with hnx
  set r : Fin s → ℕ := fun j => (Finset.univ.filter (fun k =>
    (τ k ∈ T j ∧ nx k ∈ T j) ∧ (τ k ∈ H ↔ nx k ∉ H))).card with hr
  -- Every tooth avoids some node (another tooth is disjoint from it).
  have hproper : ∀ j, T j ≠ Finset.univ := by
    intro j hj
    obtain ⟨j', hj'⟩ : ∃ j' : Fin s, j' ≠ j := by
      by_cases h0 : j.val = 0
      · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
    obtain ⟨v, hv, _⟩ := (hmeet j').1
    have := Finset.disjoint_left.mp (hdisj j' j hj') hv
    rw [hj] at this; exact this (Finset.mem_univ v)
  -- Per tooth: `2 x(E(Tⱼ)) + 1 ≤ 2 (|Tⱼ| - 1) + rⱼ`.
  have htooth : ∀ j, 2 * edgesWithin τ (T j) + 1 ≤ 2 * ((T j).card - 1) + r j := by
    intro j
    obtain ⟨p, hpT, hpH⟩ := (hmeet j).1
    obtain ⟨q, hqT, hqH⟩ := (hmeet j).2
    have hPne : (P j).Nonempty := ⟨p, by simp [hP, hpT, hpH]⟩
    have hQne : (Q j).Nonempty := ⟨q, by simp [hQ, hqT, hqH]⟩
    have hPu : P j ≠ Finset.univ := fun h => by
      have : q ∈ P j := h ▸ Finset.mem_univ q
      simp [hP] at this; exact hqH this.2
    have hQu : Q j ≠ Finset.univ := fun h => by
      have : p ∈ Q j := h ▸ Finset.mem_univ p
      simp [hQ] at this; exact this.2 hpH
    have h1 := subtour hm τ (P j) hPne hPu
    have h2 := subtour hm τ (Q j) hQne hQu
    have h3 := subtour hm τ (T j) ⟨p, hpT⟩ (hproper j)
    have hcard : (P j).card + (Q j).card = (T j).card :=
      Finset.card_filter_add_card_filter_not _
    -- Edges inside `Tⱼ` are inside `Pⱼ`, inside `Qⱼ`, or join them.
    have hsplit : edgesWithin τ (T j) = edgesWithin τ (P j) + edgesWithin τ (Q j) + r j := by
      rw [edgesWithin_eq hm, edgesWithin_eq hm, edgesWithin_eq hm, hr]
      simp only [Finset.card_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [hP, hQ, hnx, Finset.mem_filter]
      split_ifs <;> simp_all <;> tauto
    omega
  -- The joining edges of different teeth are distinct edges leaving the handle.
  have hrsum : ∑ j, r j ≤ edgesLeaving τ H := by
    rw [edgesLeaving_eq hm, hr]
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun k _ => ?_)
    by_cases hL : (τ k ∈ H ↔ nx k ∉ H)
    · rw [if_pos hL, ← Finset.card_filter]
      refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      by_contra hab
      exact Finset.disjoint_left.mp (hdisj a b hab) ha.1.1 hb.1.1
    · rw [if_neg hL]
      refine le_of_eq (Finset.sum_eq_zero (fun j _ => ?_))
      rw [if_neg]; exact fun h => hL h.2
  have hid := degree_identity hm τ H
  have hsum : 2 * ∑ j, edgesWithin τ (T j) + s ≤ 2 * ∑ j, ((T j).card - 1) + ∑ j, r j := by
    have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => htooth j)
    simpa [Finset.sum_add_distrib, Finset.mul_sum] using this
  obtain ⟨t, rfl⟩ := hsodd
  omega
