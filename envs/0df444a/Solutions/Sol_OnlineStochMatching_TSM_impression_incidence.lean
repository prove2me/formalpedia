-- Prove2me | solution 1 for OnlineStochMatching.TSM.impression_incidence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T06:09:55.718994+00:00
-- url     : https://prove2.me/submissions/6222c25b-9aac-48d5-9ce8-696a737a01cd

import Mathlib
import Definitions.Def_OnlineStochMatching_TSM_Coloring



namespace OnlineStochMatching.TSM

open Finset

variable {A I : Type}


/-- side parity -/
lemma Comp.side {F : Finset (A × I)} (C : Comp A I) (hC : C.IsPathOrCycle F) :
    ∀ j ≤ C.len, ((C.v j).isRight = (C.v 0).isRight ↔ Even j) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    obtain ⟨e, he, hed⟩ := hC.2.1 j (by omega)
    have : (C.v (j+1)).isRight ≠ (C.v j).isRight := by
      rcases hed with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
    rw [Nat.even_add_one]
    cases hA : (C.v (j+1)).isRight <;> cases hB : (C.v j).isRight <;> cases hC0 : (C.v 0).isRight <;>
      simp_all

lemma Comp.inj' {F : Finset (A × I)} (C : Comp A I) (hC : C.IsPathOrCycle F) {j₁ j₂ : ℕ}
    (h1 : j₁ ≤ C.len) (h2 : j₂ ≤ C.len) (h : C.v j₁ = C.v j₂) :
    j₁ = j₂ ∨ (C.cyc = true ∧ ((j₁ = 0 ∧ j₂ = C.len) ∨ (j₁ = C.len ∧ j₂ = 0))) := by
  have := hC.2.2
  by_cases hcy : C.cyc = true
  · simp only [hcy, if_true] at this
    obtain ⟨h4, hl, hinj⟩ := this
    by_cases a1 : j₁ = C.len
    · by_cases a2 : j₂ = C.len
      · left; omega
      · have := hinj 0 (by omega) j₂ (by omega) (by rw [← hl, ← a1]; exact h) -- v 0 = v j₂
        right; refine ⟨hcy, Or.inr ⟨a1, ?_⟩⟩; omega
    · by_cases a2 : j₂ = C.len
      · have := hinj j₁ (by omega) 0 (by omega) (by rw [h, a2, hl])
        right; refine ⟨hcy, Or.inl ⟨?_, a2⟩⟩; omega
      · left; exact hinj j₁ (by omega) j₂ (by omega) h
  · simp only [hcy] at this
    left; exact this j₁ h1 j₂ h2 h

namespace Comp

lemma hasEdge_ext (C : Comp A I) {j : ℕ} {e e' : A × I} (h : C.HasEdgeAt j e)
    (h' : C.HasEdgeAt j e') : e = e' := by
  obtain ⟨a, i⟩ := e
  obtain ⟨a', i'⟩ := e'
  unfold HasEdgeAt at h h'
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;>
    simp_all

lemma hasEdge_ep (C : Comp A I) {j : ℕ} {e : A × I} (h : C.HasEdgeAt j e) (x : A ⊕ I) :
    (x = Sum.inl e.1 ∨ x = Sum.inr e.2) ↔ (x = C.v j ∨ x = C.v (j+1)) := by
  unfold HasEdgeAt at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto

lemma hasEdge_pos {F : Finset (A × I)} (C : Comp A I) (hC : C.IsPathOrCycle F) {j j' : ℕ}
    {e : A × I} (hj : j < C.len) (hj' : j' < C.len) (h : C.HasEdgeAt j e)
    (h' : C.HasEdgeAt j' e) : j = j' := by
  have hl4 : C.cyc = true → 4 ≤ C.len := by
    intro hc; have := hC.2.2; simp only [hc, if_true] at this; exact this.1
  unfold HasEdgeAt at h h'
  have key : (C.v j = C.v j' ∧ C.v (j+1) = C.v (j'+1)) ∨ (C.v j = C.v (j'+1) ∧ C.v (j+1) = C.v j') := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · left; exact ⟨h1.trans h1'.symm, h2.trans h2'.symm⟩
    · right; exact ⟨h1.trans h2'.symm, h2.trans h1'.symm⟩
    · right; exact ⟨h1.trans h2'.symm, h2.trans h1'.symm⟩
    · left; exact ⟨h1.trans h1'.symm, h2.trans h2'.symm⟩
  rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
  · rcases C.inj' hC (by omega) (by omega) k1 with h | ⟨_, h⟩
    · exact h
    · omega
  · rcases C.inj' hC (by omega) (by omega) k1 with h | ⟨hc, h⟩ <;>
    rcases C.inj' hC (by omega) (by omega) k2 with h2 | ⟨hc2, h2⟩
    · omega
    · have := hl4 hc2; omega
    · have := hl4 hc; omega
    · have := hl4 hc; omega

lemma adj {F : Finset (A × I)} (C : Comp A I) (hC : C.IsPathOrCycle F) {j j' : ℕ} {x : A ⊕ I}
    (hj : j < C.len) (hj' : j' < C.len)
    (h : x = C.v j ∨ x = C.v (j+1)) (h' : x = C.v j' ∨ x = C.v (j'+1)) :
    j = j' ∨ j + 1 = j' ∨ j' + 1 = j ∨
      (C.cyc = true ∧ ((j = 0 ∧ j' + 1 = C.len) ∨ (j' = 0 ∧ j + 1 = C.len))) := by
  have hl4 : C.cyc = true → 4 ≤ C.len := by
    intro hc; have := hC.2.2; simp only [hc, if_true] at this; exact this.1
  have hl : C.cyc = true → C.v C.len = C.v 0 := by
    intro hc; have := hC.2.2; simp only [hc, if_true] at this; exact this.2.1
  rcases h with h | h <;> rcases h' with h' | h'
  · have e := h.symm.trans h'
    rcases C.inj' hC (by omega) (by omega) e with h | ⟨hc, h⟩ <;> first | omega | (exact Or.inr (Or.inr (Or.inr ⟨hc, by omega⟩)))
  · have e := h.symm.trans h'
    rcases C.inj' hC (by omega) (by omega) e with h | ⟨hc, h⟩ <;> first | omega | (exact Or.inr (Or.inr (Or.inr ⟨hc, by omega⟩)))
  · have e := h.symm.trans h'
    rcases C.inj' hC (by omega) (by omega) e with h | ⟨hc, h⟩ <;> first | omega | (exact Or.inr (Or.inr (Or.inr ⟨hc, by omega⟩)))
  · have e := h.symm.trans h'
    rcases C.inj' hC (by omega) (by omega) e with h | ⟨hc, h⟩ <;> first | omega | (exact Or.inr (Or.inr (Or.inr ⟨hc, by omega⟩)))

end Comp


namespace Comp

lemma blue_adj_succ (C : Comp A I) {j : ℕ} (h1 : C.BlueAt j) (h2 : C.BlueAt (j+1)) :
    C.IsEvenImpressionPath ∧ j = 0 := by
  unfold BlueAt at h1 h2
  by_cases hY : C.IsEvenImpressionPath
  · simp only [hY, true_and, not_true, false_and, or_false] at h1 h2
    refine ⟨hY, ?_⟩
    rcases h2 with h2 | h2
    · omega
    · rcases h1 with h1 | h1
      · exact h1
      · exfalso; rcases h2 with ⟨k, hk⟩; rcases h1 with ⟨l, hl⟩; omega
  · simp only [hY, false_and, false_or, not_false_eq_true, true_and] at h1 h2
    exfalso; rcases h2 with ⟨k, hk⟩; rcases h1 with ⟨l, hl⟩; omega

lemma red_adj_succ (C : Comp A I) {j : ℕ} (h1 : ¬ C.BlueAt j) (h2 : ¬ C.BlueAt (j+1)) : False := by
  unfold BlueAt at h1 h2
  by_cases hY : C.IsEvenImpressionPath
  · simp only [hY, true_and, not_true, false_and, or_false, not_or] at h1 h2
    obtain ⟨a1, a2⟩ := h1
    obtain ⟨b1, b2⟩ := h2
    apply b2
    rw [Nat.odd_iff]; rw [Nat.odd_iff] at a2; omega
  · simp only [hY, false_and, false_or, not_false_eq_true, true_and] at h1 h2
    rw [Nat.not_even_iff_odd] at h1 h2
    rcases h1 with ⟨k, hk⟩; rcases h2 with ⟨l, hl⟩; omega

lemma cyc_even {F : Finset (A × I)} (C : Comp A I) (hC : C.IsPathOrCycle F) (hc : C.cyc = true) :
    Even C.len := by
  have hl : C.v C.len = C.v 0 := by
    have := hC.2.2; simp only [hc, if_true] at this; exact this.2.1
  exact (C.side hC C.len le_rfl).1 (by rw [hl])

lemma cyc_not_Y (C : Comp A I) (hc : C.cyc = true) : ¬ C.IsEvenImpressionPath := by
  intro h; have := h.1; rw [hc] at this; simp at this

end Comp


section Col
variable [DecidableEq A] [DecidableEq I] {F blue red : Finset (A × I)}

lemma mem_verts_of {C : Comp A I} {j : ℕ} (hj : j < C.len) {x : A ⊕ I}
    (h : x = C.v j ∨ x = C.v (j+1)) : x ∈ C.verts := by
  unfold Comp.verts
  rw [Finset.mem_image]
  rcases h with h | h
  · exact ⟨j, by simp; omega, h.symm⟩
  · exact ⟨j+1, by simp; omega, h.symm⟩

lemma same_comp {m : ℕ} {C : Fin m → Comp A I}
    (hdis : ∀ k k', k ≠ k' → Disjoint (C k).verts (C k').verts)
    {k k' : Fin m} {j j' : ℕ} {x : A ⊕ I} (hj : j < (C k).len) (hj' : j' < (C k').len)
    (h : x = (C k).v j ∨ x = (C k).v (j+1)) (h' : x = (C k').v j' ∨ x = (C k').v (j'+1)) :
    k = k' := by
  by_contra hne
  have := hdis k k' hne
  exact Finset.disjoint_left.mp this (mem_verts_of hj h) (mem_verts_of hj' h')

lemma red_unique {m : ℕ} {C : Fin m → Comp A I}
    (hpc : ∀ k, (C k).IsPathOrCycle F)
    (hdis : ∀ k k', k ≠ k' → Disjoint (C k).verts (C k').verts)
    (hr : ∀ e, e ∈ red ↔ ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ ¬ (C k).BlueAt j)
    {e e' : A × I} (he : e ∈ red) (he' : e' ∈ red) {x : A ⊕ I}
    (hx : x = Sum.inl e.1 ∨ x = Sum.inr e.2) (hx' : x = Sum.inl e'.1 ∨ x = Sum.inr e'.2) :
    e = e' := by
  obtain ⟨k, j, hj, hed, hnb⟩ := (hr e).1 he
  obtain ⟨k', j', hj', hed', hnb'⟩ := (hr e').1 he'
  have h1 := (Comp.hasEdge_ep _ hed x).1 hx
  have h1' := (Comp.hasEdge_ep _ hed' x).1 hx'
  have hk := same_comp hdis hj hj' h1 h1'
  subst hk
  rcases Comp.adj _ (hpc k) hj hj' h1 h1' with h | h | h | ⟨hc, h | h⟩
  · subst h; exact Comp.hasEdge_ext _ hed hed'
  · exact (Comp.red_adj_succ _ hnb (by rw [h]; exact hnb')).elim
  · exact (Comp.red_adj_succ _ hnb' (by rw [h]; exact hnb)).elim
  · obtain ⟨h0, hl⟩ := h
    have hev := Comp.cyc_even _ (hpc k) hc
    apply False.elim
    apply hnb
    subst h0
    unfold Comp.BlueAt; right; exact ⟨Comp.cyc_not_Y _ hc, ⟨0, rfl⟩⟩
  · obtain ⟨h0, hl⟩ := h
    apply False.elim
    apply hnb'
    subst h0
    unfold Comp.BlueAt; right; exact ⟨Comp.cyc_not_Y _ hc, ⟨0, rfl⟩⟩

lemma blue_two {m : ℕ} {C : Fin m → Comp A I}
    (hpc : ∀ k, (C k).IsPathOrCycle F)
    (hdis : ∀ k k', k ≠ k' → Disjoint (C k).verts (C k').verts)
    (hb : ∀ e, e ∈ blue ↔ ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ (C k).BlueAt j)
    {e e' : A × I} (he : e ∈ blue) (he' : e' ∈ blue) (hne : e ≠ e') {x : A ⊕ I}
    (hx : x = Sum.inl e.1 ∨ x = Sum.inr e.2) (hx' : x = Sum.inl e'.1 ∨ x = Sum.inr e'.2) :
    ∃ k, (C k).IsEvenImpressionPath ∧ x = (C k).v 1 := by
  obtain ⟨k, j, hj, hed, hnb⟩ := (hb e).1 he
  obtain ⟨k', j', hj', hed', hnb'⟩ := (hb e').1 he'
  have h1 := (Comp.hasEdge_ep _ hed x).1 hx
  have h1' := (Comp.hasEdge_ep _ hed' x).1 hx'
  have hk := same_comp hdis hj hj' h1 h1'
  subst hk
  have hC := hpc k
  have hl4 : (C k).cyc = true → 4 ≤ (C k).len := by
    intro hc; have := hC.2.2; simp only [hc, if_true] at this; exact this.1
  have inj_ne : ∀ {a b : ℕ}, a ≤ (C k).len → b ≤ (C k).len → a ≠ b →
      ¬ ((C k).cyc = true ∧ ((a = 0 ∧ b = (C k).len) ∨ (a = (C k).len ∧ b = 0))) →
      (C k).v a ≠ (C k).v b := by
    intro a b ha hb hab hw hv
    rcases Comp.inj' _ hC ha hb hv with h | h
    · exact hab h
    · exact hw h
  rcases Comp.adj _ hC hj hj' h1 h1' with h | h | h | ⟨hc, h | h⟩
  · subst h; exact (hne (Comp.hasEdge_ext _ hed hed')).elim
  · subst h
    obtain ⟨hY, h0⟩ := Comp.blue_adj_succ _ hnb hnb'
    subst h0
    refine ⟨k, hY, ?_⟩
    simp only [Nat.zero_add, Nat.reduceAdd] at h1 h1'
    have n01 := inj_ne (a := 0) (b := 1) (by omega) (by omega) (by omega)
      (fun ⟨hc, h⟩ => by have := hl4 hc; omega)
    have n02 := inj_ne (a := 0) (b := 2) (by omega) (by omega) (by omega)
      (fun ⟨hc, h⟩ => by have := hl4 hc; omega)
    have n12 := inj_ne (a := 1) (b := 2) (by omega) (by omega) (by omega)
      (fun ⟨hc, h⟩ => by have := hl4 hc; omega)
    rcases h1 with h1 | h1 <;> rcases h1' with h1' | h1'
    · exact (n01 (h1.symm.trans h1')).elim
    · exact (n02 (h1.symm.trans h1')).elim
    · exact h1
    · exact (n12 (h1.symm.trans h1')).elim
  · subst h
    obtain ⟨hY, h0⟩ := Comp.blue_adj_succ _ hnb' hnb
    subst h0
    refine ⟨k, hY, ?_⟩
    simp only [Nat.zero_add, Nat.reduceAdd] at h1 h1'
    have n01 := inj_ne (a := 0) (b := 1) (by omega) (by omega) (by omega)
      (fun ⟨hc, h⟩ => by have := hl4 hc; omega)
    have n02 := inj_ne (a := 0) (b := 2) (by omega) (by omega) (by omega)
      (fun ⟨hc, h⟩ => by have := hl4 hc; omega)
    have n12 := inj_ne (a := 1) (b := 2) (by omega) (by omega) (by omega)
      (fun ⟨hc, h⟩ => by have := hl4 hc; omega)
    rcases h1 with h1 | h1 <;> rcases h1' with h1' | h1'
    · exact (n01 (h1'.symm.trans h1)).elim
    · exact h1
    · exact (n02 (h1'.symm.trans h1)).elim
    · exact (n12 (h1'.symm.trans h1)).elim
  · obtain ⟨h0, hl⟩ := h
    have hY := Comp.cyc_not_Y _ hc
    have hev := Comp.cyc_even _ hC hc
    exfalso
    unfold Comp.BlueAt at hnb'
    simp only [hY, false_and, false_or, not_false_eq_true, true_and] at hnb'
    rw [Nat.even_iff] at hnb' hev; omega
  · obtain ⟨h0, hl⟩ := h
    have hY := Comp.cyc_not_Y _ hc
    have hev := Comp.cyc_even _ hC hc
    exfalso
    unfold Comp.BlueAt at hnb
    simp only [hY, false_and, false_or, not_false_eq_true, true_and] at hnb
    rw [Nat.even_iff] at hnb hev; omega


lemma red_imp_blue {m : ℕ} {C : Fin m → Comp A I}
    (hpc : ∀ k, (C k).IsPathOrCycle F)
    (hb : ∀ e, e ∈ blue ↔ ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ (C k).BlueAt j)
    (hr : ∀ e, e ∈ red ↔ ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ ¬ (C k).BlueAt j)
    {e : A × I} (he : e ∈ red) {i : I} (hx : (Sum.inr i : A ⊕ I) = Sum.inl e.1 ∨ (Sum.inr i : A ⊕ I) = Sum.inr e.2) :
    ∃ e' ∈ blue, ((Sum.inr i : A ⊕ I) = Sum.inl e'.1 ∨ (Sum.inr i : A ⊕ I) = Sum.inr e'.2) := by
  obtain ⟨k, j, hj, hed, hnb⟩ := (hr e).1 he
  have h1 := (Comp.hasEdge_ep _ hed _).1 hx
  have hC := hpc k
  -- a blue edge at position q touching x
  have mk : ∀ q, q < (C k).len → (C k).BlueAt q → ((Sum.inr i : A ⊕ I) = (C k).v q ∨ (Sum.inr i : A ⊕ I) = (C k).v (q+1)) →
      ∃ e' ∈ blue, ((Sum.inr i : A ⊕ I) = Sum.inl e'.1 ∨ (Sum.inr i : A ⊕ I) = Sum.inr e'.2) := by
    intro q hq hbq hxq
    obtain ⟨e', _, he'⟩ := hC.2.1 q hq
    exact ⟨e', (hb e').2 ⟨k, q, hq, he', hbq⟩, (Comp.hasEdge_ep _ he' _).2 hxq⟩
  have hside := (C k).side hC
  have hlen : (C k).v ((C k).len) = (C k).v 0 → True := fun _ => trivial
  by_cases hY : (C k).IsEvenImpressionPath
  · have hev : Even (C k).len := hY.2.1
    have hnb' : ¬ (j = 0 ∨ Odd j) := by
      intro h; apply hnb; unfold Comp.BlueAt; left; exact ⟨hY, h⟩
    have hj0 : j ≠ 0 := fun h => hnb' (Or.inl h)
    have hje : Even j := by
      by_contra h; exact hnb' (Or.inr (Nat.not_even_iff_odd.1 h))
    rw [Nat.even_iff] at hje hev
    have bl : ∀ q, Odd q → (C k).BlueAt q := fun q hq => by
      unfold Comp.BlueAt; left; exact ⟨hY, Or.inr hq⟩
    rcases h1 with h | h
    · obtain ⟨q, rfl⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
      refine mk q (by omega) (bl q ?_) (Or.inr h)
      rw [Nat.odd_iff]; omega
    · refine mk (j+1) (by omega) (bl _ ?_) (Or.inl h)
      rw [Nat.odd_iff]; omega
  · have hje : Odd j := by
      by_contra h
      apply hnb; unfold Comp.BlueAt; right; exact ⟨hY, Nat.not_odd_iff_even.1 h⟩
    have bl : ∀ q, Even q → (C k).BlueAt q := fun q hq => by
      unfold Comp.BlueAt; right; exact ⟨hY, hq⟩
    rw [Nat.odd_iff] at hje
    rcases h1 with h | h
    · obtain ⟨q, rfl⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
      refine mk q (by omega) (bl q ?_) (Or.inr h)
      rw [Nat.even_iff]; omega
    · by_cases hjl : j + 1 < (C k).len
      · refine mk (j+1) hjl (bl _ ?_) (Or.inl h)
        rw [Nat.even_iff]; omega
      · have hjl' : j + 1 = (C k).len := by omega
        by_cases hc : (C k).cyc = true
        · have hl : (C k).v (C k).len = (C k).v 0 := by
            have := hC.2.2; simp only [hc, if_true] at this; exact this.2.1
          refine mk 0 (by omega) (bl 0 ⟨0, rfl⟩) (Or.inl ?_)
          rw [h, hjl', hl]
        · exfalso
          have hnc : (C k).cyc = false := by simpa using hc
          have hevl : Even (C k).len := by rw [← hjl']; rw [Nat.even_iff]; omega
          have h0 : ((C k).v 0).isRight = false := by
            cases hh : ((C k).v 0).isRight
            · rfl
            · exact (hY ⟨hnc, hevl, hh⟩).elim
          have := (hside (C k).len le_rfl).2 hevl
          rw [h0] at this
          rw [hjl'] at h
          rw [← h] at this
          simp at this

end Col

section Final
variable [DecidableEq A] [DecidableEq I]

theorem impression_incidence_core {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (F blue red : Finset (A × I)) (hcol : IsTSMColoring F blue red) (i : I) :
    (degI blue i = 0 ∧ degI red i = 0) ∨ (degI blue i = 1 ∧ degI red i = 0) ∨
      (degI blue i = 1 ∧ degI red i = 1) := by
  obtain ⟨m, C, hpc, hdis, hcov, hb, hr⟩ := hcol
  have hB : degI blue i ≤ 1 := by
    unfold degI
    rw [Finset.card_le_one]
    intro e he e' he'
    rw [Finset.mem_filter] at he he'
    by_contra hne
    obtain ⟨k, hY, hx⟩ := blue_two hpc hdis hb he.1 he'.1 hne (x := Sum.inr i)
      (Or.inr (by rw [he.2])) (Or.inr (by rw [he'.2]))
    have s := (C k).side (hpc k) 1 (by have := (hpc k).1; omega)
    have h0 : ((C k).v 0).isRight = true := hY.2.2
    rw [h0, ← hx] at s
    simp at s
  have hR : degI red i ≤ 1 := by
    unfold degI
    rw [Finset.card_le_one]
    intro e he e' he'
    rw [Finset.mem_filter] at he he'
    exact red_unique hpc hdis hr he.1 he'.1 (x := Sum.inr i)
      (Or.inr (by rw [he.2])) (Or.inr (by rw [he'.2]))
  have hRB : degI red i = 1 → degI blue i = 1 := by
    intro h1
    unfold degI at h1 ⊢
    obtain ⟨e, he⟩ := Finset.card_eq_one.1 h1
    have hm : e ∈ red.filter fun e => e.2 = i := by rw [he]; simp
    rw [Finset.mem_filter] at hm
    obtain ⟨e', he'b, hx⟩ := red_imp_blue hpc hb hr hm.1 (i := i) (Or.inr (by rw [hm.2]))
    have h2 : e'.2 = i := by
      rcases hx with hx | hx
      · simp at hx
      · simpa using hx.symm
    have : 0 < (blue.filter fun e => e.2 = i).card :=
      Finset.card_pos.2 ⟨e', Finset.mem_filter.2 ⟨he'b, h2⟩⟩
    unfold degI at hB
    omega
  unfold degI at hB hR hRB ⊢
  omega

end Final
end OnlineStochMatching.TSM

open OnlineStochMatching.TSM


theorem solution {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (E F blue red : Finset (A × I)) (hF : IsMaxFlowSet E F) (hcol : IsTSMColoring F blue red)
    (i : I) :
    (degI blue i = 0 ∧ degI red i = 0) ∨ (degI blue i = 1 ∧ degI red i = 0) ∨
      (degI blue i = 1 ∧ degI red i = 1) := by
  exact impression_incidence_core F blue red hcol i
