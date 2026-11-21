-- Prove2me | solution 1 for TwinWidthI.MinorFree.twinWidth_components
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T01:03:57.415232+00:00
-- url     : https://prove2.me/submissions/5b0f9df7-0331-42d5-8d03-c7a52f2780a0

import Mathlib
import Definitions.Def_TwinWidthI_MinorFree_Setting

namespace Aux_TwinWidthI_MinorFree_twinWidth_components

open Finset TwinWidthI.BoolWidth

/-! ## Contraction sequences as an inductive predicate -/

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
def DP (G : SimpleGraph V) {s : Finset V} (P : Finpartition s) (d : ℕ) : Prop :=
  ∀ X ∈ P.parts, #{Y ∈ P.parts | Y ≠ X ∧ ¬ Homogeneous G X Y} ≤ d

inductive Good (G : SimpleGraph V) (d : ℕ) {s : Finset V} : Finpartition s → Prop
  | fin (P : Finpartition s) : DP G P d → #P.parts ≤ 1 → Good G d P
  | step (P Q : Finpartition s) : DP G P d → IsMergeStep P Q → Good G d Q → Good G d P

theorem good_of_tw (G : SimpleGraph V) (d : ℕ) (h : TwinWidthLE G d) :
    Good G d (⊥ : Finpartition (univ : Finset V)) := by
  obtain ⟨N, P, h0, hlast, hstep, hD⟩ := h
  have key : ∀ k, (hk : k ≤ N) → Good G d (P ⟨N - k, by omega⟩) := by
    intro k
    induction k with
    | zero =>
      intro _
      have e : (⟨N - 0, by omega⟩ : Fin (N + 1)) = Fin.last N := Fin.ext (by simp)
      rw [e]
      exact Good.fin _ (hD _) hlast
    | succ k ih =>
      intro hk
      have hi := hstep ⟨N - (k + 1), by omega⟩
      have e1 : (⟨N - (k + 1), by omega⟩ : Fin N).castSucc =
          (⟨N - (k + 1), by omega⟩ : Fin (N + 1)) := rfl
      have e2 : (⟨N - (k + 1), by omega⟩ : Fin N).succ = (⟨N - k, by omega⟩ : Fin (N + 1)) :=
        Fin.ext (by simp only [Fin.val_succ]; omega)
      rw [e1, e2] at hi
      exact Good.step _ _ (hD _) hi (ih (by omega))
  have h1 := key N le_rfl
  have e0 : (⟨N - N, by omega⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
  rw [e0, h0] at h1
  exact h1

theorem tw_of_good (G : SimpleGraph V) (d : ℕ) {P : Finpartition (univ : Finset V)}
    (h : Good G d P) :
    ∃ (N : ℕ) (Ps : Fin (N + 1) → Finpartition (univ : Finset V)),
      Ps 0 = P ∧ #(Ps (Fin.last N)).parts ≤ 1 ∧
      (∀ i : Fin N, IsMergeStep (Ps i.castSucc) (Ps i.succ)) ∧ ∀ i, DP G (Ps i) d := by
  induction h with
  | fin P hD hc => exact ⟨0, fun _ => P, rfl, hc, fun i => i.elim0, fun _ => hD⟩
  | step P Q hD hm _ ih =>
    obtain ⟨N, Ps, h0, hl, hs, hd⟩ := ih
    refine ⟨N + 1, (Fin.cons P Ps : Fin (N + 1 + 1) → Finpartition (univ : Finset V)),
      Fin.cons_zero _ _, ?_, ?_, ?_⟩
    · have e : Fin.last (N + 1) = (Fin.last N).succ := rfl
      rw [e, Fin.cons_succ]
      exact hl
    · intro i
      induction i using Fin.cases with
      | zero =>
        simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, h0]
        exact hm
      | succ j =>
        rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
        exact hs j
    · intro i
      induction i using Fin.cases with
      | zero =>
        rw [Fin.cons_zero]
        exact hD
      | succ j =>
        rw [Fin.cons_succ]
        exact hd j

lemma hom_mono {G : SimpleGraph V} {X Y X' Y' : Finset V} (h : Homogeneous G X Y)
    (hX : X' ⊆ X) (hY : Y' ⊆ Y) : Homogeneous G X' Y' := by
  rcases h with h | h
  · left
    intro x hx y hy
    exact h x (hX hx) y (hY hy)
  · right
    intro x hx y hy
    exact h x (hX hx) y (hY hy)

lemma DP_bot (G : SimpleGraph V) (d : ℕ) (s : Finset V) : DP G (⊥ : Finpartition s) d := by
  classical
  intro X hX
  simp only [Finpartition.parts_bot, Finset.mem_map, Function.Embedding.coeFn_mk] at hX
  obtain ⟨a, _, rfl⟩ := hX
  refine le_trans (le_of_eq (Finset.card_eq_zero.mpr ?_)) (Nat.zero_le d)
  rw [Finset.filter_eq_empty_iff]
  intro Y hY
  simp only [Finpartition.parts_bot, Finset.mem_map, Function.Embedding.coeFn_mk] at hY
  obtain ⟨b, _, rfl⟩ := hY
  intro hh
  apply hh.2
  by_cases hab : G.Adj a b
  · left
    intro x hx y hy
    rw [Finset.mem_singleton] at hx hy
    subst hx
    subst hy
    exact hab
  · right
    intro x hx y hy
    rw [Finset.mem_singleton] at hx hy
    subst hx
    subst hy
    exact hab

/-! ## Transfer along a part map -/

theorem transfer {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph V)
    (H : SimpleGraph W) (d : ℕ) {a : Finset V} {b : Finset W}
    (Φ : Finpartition a → Finpartition b) (φ : Finset V → Finset W)
    (hparts : ∀ P, (Φ P).parts = P.parts.image φ)
    (hinj : ∀ X ⊆ a, ∀ Y ⊆ a, φ X = φ Y → X = Y)
    (hunion : ∀ X Y, φ (X ∪ Y) = φ X ∪ φ Y)
    (hhom : ∀ X ⊆ a, ∀ Y ⊆ a, (Homogeneous H (φ X) (φ Y) ↔ Homogeneous G X Y)) :
    ∀ P : Finpartition a, Good G d P → Good H d (Φ P) := by
  classical
  have hDP : ∀ P : Finpartition a, DP G P d → DP H (Φ P) d := by
    intro P hP X' hX'
    rw [hparts] at hX'
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hX'
    have h1 := hP X hX
    refine le_trans (Finset.card_le_card ?_) ((Finset.card_image_le (f := φ)).trans h1)
    intro Y' hY'
    rw [Finset.mem_filter, hparts, Finset.mem_image] at hY'
    obtain ⟨⟨Y, hY, rfl⟩, hne, hnh⟩ := hY'
    refine Finset.mem_image.mpr ⟨Y, Finset.mem_filter.mpr ⟨hY, ?_, ?_⟩, rfl⟩
    · rintro rfl
      exact hne rfl
    · intro hh
      exact hnh ((hhom X (P.le hX) Y (P.le hY)).mpr hh)
  have hmerge : ∀ P Q : Finpartition a, IsMergeStep P Q → IsMergeStep (Φ P) (Φ Q) := by
    rintro P Q ⟨X, hX, Y, hY, hXY, hQ⟩
    refine ⟨φ X, ?_, φ Y, ?_, ?_, ?_⟩
    · rw [hparts]
      exact Finset.mem_image_of_mem φ hX
    · rw [hparts]
      exact Finset.mem_image_of_mem φ hY
    · intro hh
      exact hXY (hinj X (P.le hX) Y (P.le hY) hh)
    · rw [hparts, hparts, hQ]
      ext W
      simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨Z, hZ, rfl⟩
        rcases hZ with rfl | ⟨hZY, hZX, hZ⟩
        · left
          exact hunion X Y
        · right
          refine ⟨?_, ?_, Z, hZ, rfl⟩
          · intro hh
            exact hZY (hinj Z (P.le hZ) Y (P.le hY) hh)
          · intro hh
            exact hZX (hinj Z (P.le hZ) X (P.le hX) hh)
      · rintro (rfl | ⟨hWY, hWX, Z, hZ, rfl⟩)
        · exact ⟨X ∪ Y, Or.inl rfl, hunion X Y⟩
        · refine ⟨Z, Or.inr ⟨?_, ?_, hZ⟩, rfl⟩
          · rintro rfl
            exact hWY rfl
          · rintro rfl
            exact hWX rfl
  intro P hP
  induction hP with
  | fin P hD hc =>
    refine Good.fin _ (hDP P hD) (le_trans ?_ hc)
    rw [hparts]
    exact Finset.card_image_le
  | step P Q hD hm _ ih => exact Good.step _ _ (hDP P hD) (hmerge P Q hm) ih

/-! ## Restriction to a vertex subset -/

lemma restrict_parts {s t : Finset V} (P : Finpartition s) (h : t ≤ s) :
    (P.restrict h).parts = (P.parts.image (fun X => X ∩ t)).erase ∅ := rfl

lemma mem_restrict {s t : Finset V} (P : Finpartition s) (h : t ≤ s) (W : Finset V) :
    W ∈ (P.restrict h).parts ↔ W ≠ ∅ ∧ ∃ X ∈ P.parts, X ∩ t = W := by
  rw [restrict_parts, Finset.mem_erase, Finset.mem_image]

lemma DP_restrict (G : SimpleGraph V) (d : ℕ) {s t : Finset V} (P : Finpartition s) (h : t ≤ s)
    (hP : DP G P d) : DP G (P.restrict h) d := by
  classical
  intro W hW
  obtain ⟨_, X, hX, rfl⟩ := (mem_restrict P h W).mp hW
  have h1 := hP X hX
  refine le_trans (Finset.card_le_card ?_)
    ((Finset.card_image_le (f := fun Z => Z ∩ t)).trans h1)
  intro Z' hZ'
  rw [Finset.mem_filter] at hZ'
  obtain ⟨hZ'm, hne, hnh⟩ := hZ'
  obtain ⟨_, Z, hZ, rfl⟩ := (mem_restrict P h Z').mp hZ'm
  refine Finset.mem_image.mpr ⟨Z, Finset.mem_filter.mpr ⟨hZ, ?_, ?_⟩, rfl⟩
  · rintro rfl
    exact hne rfl
  · intro hh
    exact hnh (hom_mono hh Finset.inter_subset_left Finset.inter_subset_left)

lemma card_restrict {s t : Finset V} (P : Finpartition s) (h : t ≤ s) :
    #(P.restrict h).parts ≤ #P.parts := by
  rw [restrict_parts]
  exact (Finset.card_erase_le).trans Finset.card_image_le

lemma merge_restrict {s t : Finset V} (P Q : Finpartition s) (h : t ≤ s)
    (hm : IsMergeStep P Q) :
    Q.restrict h = P.restrict h ∨ IsMergeStep (P.restrict h) (Q.restrict h) := by
  obtain ⟨X, hX, Y, hY, hXY, hQ⟩ := hm
  have hQmem : ∀ Z, Z ∈ Q.parts ↔ Z = X ∪ Y ∨ (Z ≠ Y ∧ Z ≠ X ∧ Z ∈ P.parts) := by
    intro Z
    rw [hQ, Finset.mem_insert, Finset.mem_erase, Finset.mem_erase]
  have hU : (X ∪ Y) ∩ t = X ∩ t ∪ Y ∩ t := Finset.union_inter_distrib_right X Y t
  by_cases hXt : X ∩ t = ∅
  · left
    ext W
    rw [mem_restrict, mem_restrict]
    constructor
    · rintro ⟨hW0, Z, hZ, rfl⟩
      rcases (hQmem Z).mp hZ with rfl | ⟨_, _, hZP⟩
      · exact ⟨hW0, Y, hY, by rw [hU, hXt, Finset.empty_union]⟩
      · exact ⟨hW0, Z, hZP, rfl⟩
    · rintro ⟨hW0, Z, hZ, rfl⟩
      by_cases hZX : Z = X
      · exact (hW0 (by rw [hZX]; exact hXt)).elim
      by_cases hZY : Z = Y
      · exact ⟨hW0, X ∪ Y, (hQmem _).mpr (Or.inl rfl),
          by rw [hU, hXt, Finset.empty_union, hZY]⟩
      · exact ⟨hW0, Z, (hQmem Z).mpr (Or.inr ⟨hZY, hZX, hZ⟩), rfl⟩
  by_cases hYt : Y ∩ t = ∅
  · left
    ext W
    rw [mem_restrict, mem_restrict]
    constructor
    · rintro ⟨hW0, Z, hZ, rfl⟩
      rcases (hQmem Z).mp hZ with rfl | ⟨_, _, hZP⟩
      · exact ⟨hW0, X, hX, by rw [hU, hYt, Finset.union_empty]⟩
      · exact ⟨hW0, Z, hZP, rfl⟩
    · rintro ⟨hW0, Z, hZ, rfl⟩
      by_cases hZY : Z = Y
      · exact (hW0 (by rw [hZY]; exact hYt)).elim
      by_cases hZX : Z = X
      · exact ⟨hW0, X ∪ Y, (hQmem _).mpr (Or.inl rfl),
          by rw [hU, hYt, Finset.union_empty, hZX]⟩
      · exact ⟨hW0, Z, (hQmem Z).mpr (Or.inr ⟨hZY, hZX, hZ⟩), rfl⟩
  right
  have hXt' : (X ∩ t).Nonempty := Finset.nonempty_iff_ne_empty.mpr hXt
  have hne : X ∩ t ≠ Y ∩ t := by
    intro heq
    obtain ⟨z, hz⟩ := hXt'
    have hz' : z ∈ Y ∩ t := heq ▸ hz
    exact hXY (P.eq_of_mem_parts hX hY (Finset.mem_inter.mp hz).1 (Finset.mem_inter.mp hz').1)
  refine ⟨X ∩ t, (mem_restrict P h _).mpr ⟨hXt, X, hX, rfl⟩, Y ∩ t,
    (mem_restrict P h _).mpr ⟨hYt, Y, hY, rfl⟩, hne, ?_⟩
  ext W
  rw [mem_restrict, Finset.mem_insert, Finset.mem_erase, Finset.mem_erase, mem_restrict]
  constructor
  · rintro ⟨hW0, Z, hZ, rfl⟩
    rcases (hQmem Z).mp hZ with rfl | ⟨hZY, hZX, hZP⟩
    · left
      exact hU
    · right
      refine ⟨?_, ?_, hW0, Z, hZP, rfl⟩
      · intro heq
        obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hW0
        have hz' : z ∈ Y ∩ t := heq ▸ hz
        exact hZY (P.eq_of_mem_parts hZP hY (Finset.mem_inter.mp hz).1
          (Finset.mem_inter.mp hz').1)
      · intro heq
        obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hW0
        have hz' : z ∈ X ∩ t := heq ▸ hz
        exact hZX (P.eq_of_mem_parts hZP hX (Finset.mem_inter.mp hz).1
          (Finset.mem_inter.mp hz').1)
  · rintro (rfl | ⟨hWY, hWX, hW0, Z, hZ, rfl⟩)
    · refine ⟨?_, X ∪ Y, (hQmem _).mpr (Or.inl rfl), hU⟩
      rw [← Finset.nonempty_iff_ne_empty]
      exact hXt'.mono Finset.subset_union_left
    · refine ⟨hW0, Z, (hQmem Z).mpr (Or.inr ⟨?_, ?_, hZ⟩), rfl⟩
      · rintro rfl
        exact hWY rfl
      · rintro rfl
        exact hWX rfl

lemma good_restrict (G : SimpleGraph V) (d : ℕ) {s t : Finset V} (h : t ≤ s) :
    ∀ P : Finpartition s, Good G d P → Good G d (P.restrict h) := by
  intro P hP
  induction hP with
  | fin P hD hc => exact Good.fin _ (DP_restrict G d P h hD) ((card_restrict P h).trans hc)
  | step P Q hD hm _ ih =>
    rcases merge_restrict P Q h hm with heq | hm'
    · rw [← heq]
      exact ih
    · exact Good.step _ _ (DP_restrict G d P h hD) hm' ih

lemma bot_restrict {s t : Finset V} (h : t ≤ s) :
    (⊥ : Finpartition s).restrict h = ⊥ := by
  ext W
  rw [mem_restrict]
  simp only [Finpartition.parts_bot, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hW0, X, ⟨a, _, rfl⟩, rfl⟩
    by_cases hat : a ∈ t
    · exact ⟨a, hat, (Finset.singleton_inter_of_mem hat).symm⟩
    · exact (hW0 (Finset.singleton_inter_of_notMem hat)).elim
  · rintro ⟨a, hat, rfl⟩
    exact ⟨Finset.singleton_ne_empty a, {a}, ⟨a, h hat, rfl⟩, Finset.singleton_inter_of_mem hat⟩

/-! ## Disjoint sums of partitions -/

def psum {s t : Finset V} (hst : Disjoint s t) (P : Finpartition s) (Q : Finpartition t) :
    Finpartition (s ∪ t) :=
  Finpartition.ofExistsUnique (P.parts ∪ Q.parts)
    (by
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact Finset.Subset.trans (P.le hp) Finset.subset_union_left
      · exact Finset.Subset.trans (Q.le hp) Finset.subset_union_right)
    (by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨W, ⟨hW, hxW⟩, hu⟩ := P.existsUnique_mem hx
        refine ⟨W, ⟨Finset.mem_union_left _ hW, hxW⟩, ?_⟩
        rintro W' ⟨hW', hxW'⟩
        rcases Finset.mem_union.mp hW' with hW' | hW'
        · exact hu W' ⟨hW', hxW'⟩
        · exact absurd (Q.le hW' hxW') (Finset.disjoint_left.mp hst hx)
      · obtain ⟨W, ⟨hW, hxW⟩, hu⟩ := Q.existsUnique_mem hx
        refine ⟨W, ⟨Finset.mem_union_right _ hW, hxW⟩, ?_⟩
        rintro W' ⟨hW', hxW'⟩
        rcases Finset.mem_union.mp hW' with hW' | hW'
        · exact absurd (P.le hW' hxW') (Finset.disjoint_right.mp hst hx)
        · exact hu W' ⟨hW', hxW'⟩)
    (by
      rw [Finset.mem_union]
      rintro (h | h)
      · exact P.empty_notMem_parts h
      · exact Q.empty_notMem_parts h)

lemma psum_parts {s t : Finset V} (hst : Disjoint s t) (P : Finpartition s)
    (Q : Finpartition t) : (psum hst P Q).parts = P.parts ∪ Q.parts := rfl

lemma DP_psum (G : SimpleGraph V) (d : ℕ) {s t : Finset V} (hst : Disjoint s t)
    (hno : ∀ x ∈ s, ∀ y ∈ t, ¬ G.Adj x y) (P : Finpartition s) (Q : Finpartition t)
    (hP : DP G P d) (hQ : DP G Q d) : DP G (psum hst P Q) d := by
  classical
  intro X hX
  rw [psum_parts] at hX
  rcases Finset.mem_union.mp hX with hX | hX
  · refine le_trans (Finset.card_le_card ?_) (hP X hX)
    intro Y hY
    rw [Finset.mem_filter, psum_parts, Finset.mem_union] at hY
    obtain ⟨hYm, hne, hnh⟩ := hY
    refine Finset.mem_filter.mpr ⟨?_, hne, hnh⟩
    rcases hYm with hYm | hYm
    · exact hYm
    · exact (hnh (Or.inr (fun x hx y hy => hno x (P.le hX hx) y (Q.le hYm hy)))).elim
  · refine le_trans (Finset.card_le_card ?_) (hQ X hX)
    intro Y hY
    rw [Finset.mem_filter, psum_parts, Finset.mem_union] at hY
    obtain ⟨hYm, hne, hnh⟩ := hY
    refine Finset.mem_filter.mpr ⟨?_, hne, hnh⟩
    rcases hYm with hYm | hYm
    · exact (hnh (Or.inr (fun x hx y hy hxy =>
        hno y (P.le hYm hy) x (Q.le hX hx) hxy.symm))).elim
    · exact hYm

lemma not_mem_of_disj {s t : Finset V} (hst : Disjoint s t) (P : Finpartition s)
    (Q : Finpartition t) {X : Finset V} (hX : X ∈ P.parts) : X ∉ Q.parts := by
  intro hq
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hX
  exact Finset.disjoint_left.mp hst (P.le hX hx) (Q.le hq hx)

lemma merge_psum_left {s t : Finset V} (hst : Disjoint s t) (P P' : Finpartition s)
    (Q : Finpartition t) (hm : IsMergeStep P P') :
    IsMergeStep (psum hst P Q) (psum hst P' Q) := by
  obtain ⟨X, hX, Y, hY, hXY, hP'⟩ := hm
  have hXQ := not_mem_of_disj hst P Q hX
  have hYQ := not_mem_of_disj hst P Q hY
  refine ⟨X, ?_, Y, ?_, hXY, ?_⟩
  · rw [psum_parts]
    exact Finset.mem_union_left _ hX
  · rw [psum_parts]
    exact Finset.mem_union_left _ hY
  · rw [psum_parts, psum_parts, hP']
    ext W
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ((hh | ⟨h1, h2, h3⟩) | hh)
      · exact Or.inl hh
      · exact Or.inr ⟨h1, h2, Or.inl h3⟩
      · exact Or.inr ⟨fun e => hYQ (by rw [← e]; exact hh),
          fun e => hXQ (by rw [← e]; exact hh), Or.inr hh⟩
    · rintro (hh | ⟨h1, h2, h3 | h3⟩)
      · exact Or.inl (Or.inl hh)
      · exact Or.inl (Or.inr ⟨h1, h2, h3⟩)
      · exact Or.inr h3

lemma merge_psum_right {s t : Finset V} (hst : Disjoint s t) (P : Finpartition s)
    (Q Q' : Finpartition t) (hm : IsMergeStep Q Q') :
    IsMergeStep (psum hst P Q) (psum hst P Q') := by
  obtain ⟨X, hX, Y, hY, hXY, hQ'⟩ := hm
  have hXP := not_mem_of_disj hst.symm Q P hX
  have hYP := not_mem_of_disj hst.symm Q P hY
  refine ⟨X, ?_, Y, ?_, hXY, ?_⟩
  · rw [psum_parts]
    exact Finset.mem_union_right _ hX
  · rw [psum_parts]
    exact Finset.mem_union_right _ hY
  · rw [psum_parts, psum_parts, hQ']
    ext W
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro (hh | (hh | ⟨h1, h2, h3⟩))
      · exact Or.inr ⟨fun e => hYP (by rw [← e]; exact hh),
          fun e => hXP (by rw [← e]; exact hh), Or.inl hh⟩
      · exact Or.inl hh
      · exact Or.inr ⟨h1, h2, Or.inr h3⟩
    · rintro (hh | ⟨h1, h2, h3 | h3⟩)
      · exact Or.inr (Or.inl hh)
      · exact Or.inl h3
      · exact Or.inr (Or.inr ⟨h1, h2, h3⟩)

lemma psum_bot {s t : Finset V} (hst : Disjoint s t) :
    psum hst (⊥ : Finpartition s) (⊥ : Finpartition t) = ⊥ := by
  ext W
  rw [psum_parts]
  simp only [Finpartition.parts_bot, Finset.mem_union, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨a, Or.inl ha, rfl⟩
    · exact ⟨a, Or.inr ha, rfl⟩
  · rintro ⟨a, ha | ha, rfl⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨a, ha, rfl⟩

lemma card_psum {s t : Finset V} (hst : Disjoint s t) (P : Finpartition s)
    (Q : Finpartition t) : #(psum hst P Q).parts ≤ #P.parts + #Q.parts := by
  rw [psum_parts]
  exact Finset.card_union_le _ _

lemma phase2 (G : SimpleGraph V) (d : ℕ) {s t : Finset V} (hst : Disjoint s t)
    (hno : ∀ x ∈ s, ∀ y ∈ t, ¬ G.Adj x y) (P : Finpartition s) (hP : DP G P d)
    (hP1 : #P.parts ≤ 1) :
    ∀ Q : Finpartition t, Good G d Q → Good G d (psum hst P Q) := by
  classical
  intro Q hQ
  induction hQ with
  | fin Q hD hc =>
    have hDs := DP_psum G d hst hno P Q hP hD
    by_cases h1 : #(psum hst P Q).parts ≤ 1
    · exact Good.fin _ hDs h1
    · have h2 : #(psum hst P Q).parts = 2 := by
        have := card_psum hst P Q
        omega
      obtain ⟨A, B, hAB, hparts⟩ := Finset.card_eq_two.mp h2
      have hA : A ∈ (psum hst P Q).parts := by
        rw [hparts]
        exact Finset.mem_insert_self A {B}
      have hB : B ∈ (psum hst P Q).parts := by
        rw [hparts]
        simp
      have hne : s ∪ t ≠ ∅ := by
        obtain ⟨x, hx⟩ := (psum hst P Q).nonempty_of_mem_parts hA
        exact Finset.ne_empty_of_mem ((psum hst P Q).le hA hx)
      have hAB' : A ∪ B = s ∪ t := by
        have := (psum hst P Q).biUnion_parts
        rw [hparts] at this
        simpa [Finset.biUnion_insert] using this
      refine Good.step _ (Finpartition.indiscrete hne) hDs ⟨A, hA, B, hB, hAB, ?_⟩
        (Good.fin _ ?_ ?_)
      · rw [Finpartition.indiscrete_parts, hparts,
          Finset.erase_insert (by simpa using hAB), Finset.erase_singleton, Finset.insert_empty,
          hAB']
      · intro X hX
        rw [Finpartition.indiscrete_parts, Finset.mem_singleton] at hX
        refine le_trans (le_of_eq (Finset.card_eq_zero.mpr ?_)) (Nat.zero_le d)
        rw [Finset.filter_eq_empty_iff]
        intro Y hY hh
        rw [Finpartition.indiscrete_parts, Finset.mem_singleton] at hY
        exact hh.1 (hY.trans hX.symm)
      · rw [Finpartition.indiscrete_parts, Finset.card_singleton]
  | step Q Q' hD hm _ ih =>
    exact Good.step _ _ (DP_psum G d hst hno P Q hP hD) (merge_psum_right hst P Q Q' hm) ih

lemma phase1 (G : SimpleGraph V) (d : ℕ) {s t : Finset V} (hst : Disjoint s t)
    (hno : ∀ x ∈ s, ∀ y ∈ t, ¬ G.Adj x y) (Q0 : Good G d (⊥ : Finpartition t)) :
    ∀ P : Finpartition s, Good G d P → Good G d (psum hst P ⊥) := by
  intro P hP
  induction hP with
  | fin P hD hc => exact phase2 G d hst hno P hD hc ⊥ Q0
  | step P P' hD hm _ ih =>
    exact Good.step _ _ (DP_psum G d hst hno P ⊥ hD (DP_bot G d t))
      (merge_psum_left hst P P' ⊥ hm) ih

lemma glue (G : SimpleGraph V) (d : ℕ) {s t : Finset V} (hst : Disjoint s t)
    (hno : ∀ x ∈ s, ∀ y ∈ t, ¬ G.Adj x y) (hs : Good G d (⊥ : Finpartition s))
    (ht : Good G d (⊥ : Finpartition t)) : Good G d (⊥ : Finpartition (s ∪ t)) := by
  have h := phase1 G d hst hno ht ⊥ hs
  rw [psum_bot] at h
  exact h

end General

/-! ## Induced subgraphs on a vertex set -/

section Sub

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
noncomputable def sF (S : Set V) : Finset V := univ.filter (fun v => v ∈ S)

lemma mem_sF (S : Set V) (v : V) : v ∈ sF S ↔ v ∈ S := by
  unfold sF
  simp

def liftF (S : Set V) (X : Finset S) : Finset V := X.map (Function.Embedding.subtype _)

open Classical in
noncomputable def lowF (S : Set V) (Y : Finset V) : Finset S := Y.subtype (fun v => v ∈ S)

lemma mem_lowF (S : Set V) (Y : Finset V) (x : S) : x ∈ lowF S Y ↔ (x : V) ∈ Y := by
  classical
  unfold lowF
  rw [Finset.mem_subtype]

variable (S : Set V) [instF : Fintype S] [instD : DecidableEq S]

noncomputable def liftP (P : Finpartition (univ : Finset S)) : Finpartition (sF S) :=
  Finpartition.ofExistsUnique (P.parts.image (liftF S))
    (by
      intro p hp
      obtain ⟨X, _, rfl⟩ := Finset.mem_image.mp hp
      intro v hv
      obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hv
      exact (mem_sF S _).mpr x.2)
    (by
      intro v hv
      have hvS : v ∈ S := (mem_sF S v).mp hv
      obtain ⟨X, ⟨hX, hxX⟩, hu⟩ := P.existsUnique_mem (Finset.mem_univ (⟨v, hvS⟩ : S))
      refine ⟨liftF S X, ⟨Finset.mem_image_of_mem _ hX,
        Finset.mem_map.mpr ⟨⟨v, hvS⟩, hxX, rfl⟩⟩, ?_⟩
      rintro Y ⟨hY, hvY⟩
      obtain ⟨X', hX', rfl⟩ := Finset.mem_image.mp hY
      obtain ⟨x, hx, hxv⟩ := Finset.mem_map.mp hvY
      have hxe : x = ⟨v, hvS⟩ := Subtype.ext hxv
      subst hxe
      rw [hu X' ⟨hX', hx⟩])
    (by
      intro h
      obtain ⟨X, hX, hX0⟩ := Finset.mem_image.mp h
      have hXe : X = ∅ := Finset.map_eq_empty.mp hX0
      rw [hXe] at hX
      exact P.empty_notMem_parts hX)

noncomputable def lowP (Q : Finpartition (sF S)) : Finpartition (univ : Finset S) :=
  Finpartition.ofExistsUnique (Q.parts.image (lowF S))
    (fun p _ => Finset.subset_univ p)
    (by
      intro x _
      have hx : (x : V) ∈ sF S := (mem_sF S x).mpr x.2
      obtain ⟨Y, ⟨hY, hxY⟩, hu⟩ := Q.existsUnique_mem hx
      refine ⟨lowF S Y, ⟨Finset.mem_image_of_mem _ hY, (mem_lowF S Y x).mpr hxY⟩, ?_⟩
      rintro Z ⟨hZ, hxZ⟩
      obtain ⟨Y', hY', rfl⟩ := Finset.mem_image.mp hZ
      rw [mem_lowF] at hxZ
      rw [hu Y' ⟨hY', hxZ⟩])
    (by
      intro h
      obtain ⟨Y, hY, hY0⟩ := Finset.mem_image.mp h
      obtain ⟨y, hy⟩ := Q.nonempty_of_mem_parts hY
      have hyS : y ∈ S := (mem_sF S y).mp (Q.le hY hy)
      have hmem : (⟨y, hyS⟩ : S) ∈ lowF S Y := (mem_lowF S Y _).mpr hy
      rw [hY0] at hmem
      exact Finset.notMem_empty _ hmem)

lemma lift_bot : liftP S (⊥ : Finpartition (univ : Finset S)) = ⊥ := by
  ext W
  unfold liftP
  simp only [Finpartition.ofExistsUnique_parts, Finpartition.parts_bot, Finset.mem_image,
    Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨X, ⟨x, _, rfl⟩, rfl⟩
    exact ⟨x, (mem_sF S _).mpr x.2, by simp [liftF]⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨{⟨v, (mem_sF S v).mp hv⟩}, ⟨⟨v, (mem_sF S v).mp hv⟩, Finset.mem_univ _, rfl⟩,
      by simp [liftF]⟩

lemma low_bot : lowP S (⊥ : Finpartition (sF S)) = ⊥ := by
  ext W
  unfold lowP
  simp only [Finpartition.ofExistsUnique_parts, Finpartition.parts_bot, Finset.mem_image,
    Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨Y, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨⟨v, (mem_sF S v).mp hv⟩, Finset.mem_univ _, ?_⟩
    ext x
    rw [mem_lowF, Finset.mem_singleton, Finset.mem_singleton]
    constructor
    · intro hx
      rw [hx]
    · intro hx
      exact Subtype.ext hx
  · rintro ⟨x, _, rfl⟩
    refine ⟨{(x : V)}, ⟨x, (mem_sF S x).mpr x.2, rfl⟩, ?_⟩
    ext y
    rw [mem_lowF, Finset.mem_singleton, Finset.mem_singleton]
    constructor
    · intro hy
      exact Subtype.ext hy
    · intro hy
      rw [hy]

lemma hom_lift (G : SimpleGraph V) : ∀ X ⊆ (univ : Finset S), ∀ Y ⊆ (univ : Finset S),
    (Homogeneous G (liftF S X) (liftF S Y) ↔ Homogeneous (G.induce S) X Y) := by
  intro X _ Y _
  unfold Homogeneous liftF
  constructor
  · rintro (h | h)
    · left
      intro x hx y hy
      exact h _ (Finset.mem_map_of_mem _ hx) _ (Finset.mem_map_of_mem _ hy)
    · right
      intro x hx y hy
      exact h _ (Finset.mem_map_of_mem _ hx) _ (Finset.mem_map_of_mem _ hy)
  · rintro (h | h)
    · left
      intro x' hx' y' hy'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hx'
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hy'
      exact h x hx y hy
    · right
      intro x' hx' y' hy'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hx'
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hy'
      exact h x hx y hy

lemma hom_low (G : SimpleGraph V) : ∀ X ⊆ sF S, ∀ Y ⊆ sF S,
    (Homogeneous (G.induce S) (lowF S X) (lowF S Y) ↔ Homogeneous G X Y) := by
  intro X hX Y hY
  unfold Homogeneous
  constructor
  · rintro (h | h)
    · left
      intro x hx y hy
      exact h ⟨x, (mem_sF S x).mp (hX hx)⟩ ((mem_lowF S X _).mpr hx)
        ⟨y, (mem_sF S y).mp (hY hy)⟩ ((mem_lowF S Y _).mpr hy)
    · right
      intro x hx y hy
      exact h ⟨x, (mem_sF S x).mp (hX hx)⟩ ((mem_lowF S X _).mpr hx)
        ⟨y, (mem_sF S y).mp (hY hy)⟩ ((mem_lowF S Y _).mpr hy)
  · rintro (h | h)
    · left
      intro x hx y hy
      exact h _ ((mem_lowF S X x).mp hx) _ ((mem_lowF S Y y).mp hy)
    · right
      intro x hx y hy
      exact h _ ((mem_lowF S X x).mp hx) _ ((mem_lowF S Y y).mp hy)

lemma low_inj : ∀ X ⊆ sF S, ∀ Y ⊆ sF S, lowF S X = lowF S Y → X = Y := by
  classical
  intro X hX Y hY hXY
  have e1 : (lowF S X).map (Function.Embedding.subtype _) = X := by
    unfold lowF
    exact Finset.subtype_map_of_mem (fun x hx => (mem_sF S x).mp (hX hx))
  have e2 : (lowF S Y).map (Function.Embedding.subtype _) = Y := by
    unfold lowF
    exact Finset.subtype_map_of_mem (fun x hx => (mem_sF S x).mp (hY hx))
  rw [← e1, ← e2, hXY]

lemma low_union : ∀ X Y : Finset V, lowF S (X ∪ Y) = lowF S X ∪ lowF S Y := by
  intro X Y
  ext x
  rw [Finset.mem_union, mem_lowF, mem_lowF, mem_lowF, Finset.mem_union]

lemma sub_iff (G : SimpleGraph V) (d : ℕ) :
    TwinWidthLE (G.induce S) d ↔ Good G d (⊥ : Finpartition (sF S)) := by
  constructor
  · intro h
    have h1 := good_of_tw (G.induce S) d h
    have h2 := transfer (G.induce S) G d (liftP S) (liftF S) (fun P => rfl)
      (fun X _ Y _ hXY => Finset.map_injective _ hXY)
      (fun X Y => by unfold liftF; exact Finset.map_union _ _) (hom_lift S G) ⊥ h1
    rw [lift_bot] at h2
    exact h2
  · intro h
    have h2 := transfer G (G.induce S) d (lowP S) (lowF S) (fun Q => rfl) (low_inj S)
      (low_union S) (hom_low S G) ⊥ h
    rw [low_bot] at h2
    obtain ⟨N, Ps, h0, hl, hs, hd⟩ := tw_of_good (G.induce S) d h2
    exact ⟨N, Ps, h0, hl, hs, hd⟩

end Sub

/-! ## Components -/

section Comp

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma good_union (G : SimpleGraph V) (d : ℕ)
    (h : ∀ c : G.ConnectedComponent, Good G d (⊥ : Finpartition (sF c.supp))) :
    Good G d (⊥ : Finpartition (univ : Finset V)) := by
  classical
  have key : ∀ I : Finset G.ConnectedComponent,
      Good G d (⊥ : Finpartition (I.biUnion (fun c => sF c.supp))) := by
    intro I
    induction I using Finset.induction_on with
    | empty =>
      rw [Finset.biUnion_empty]
      exact Good.fin _ (DP_bot G d _) (by rw [Finpartition.card_bot]; simp)
    | insert c I hc ih =>
      rw [Finset.biUnion_insert]
      refine glue G d ?_ ?_ (h c) ih
      · rw [Finset.disjoint_left]
        intro v hv hv'
        rw [Finset.mem_biUnion] at hv'
        obtain ⟨c', hc', hv'⟩ := hv'
        rw [mem_sF, SimpleGraph.ConnectedComponent.mem_supp_iff] at hv hv'
        exact hc (by rw [← hv, hv']; exact hc')
      · intro x hx y hy hxy
        rw [Finset.mem_biUnion] at hy
        obtain ⟨c', hc', hy⟩ := hy
        rw [mem_sF, SimpleGraph.ConnectedComponent.mem_supp_iff] at hx hy
        have hxy' : G.connectedComponentMk x = G.connectedComponentMk y :=
          SimpleGraph.ConnectedComponent.sound hxy.reachable
        exact hc (by rw [← hx, hxy', hy]; exact hc')
  have hU : (Finset.univ.image G.connectedComponentMk).biUnion (fun c => sF c.supp) = univ := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact ⟨_, ⟨v, rfl⟩, (mem_sF _ v).mpr rfl⟩
  have h1 := key (Finset.univ.image G.connectedComponentMk)
  rw [hU] at h1
  exact h1

end Comp

end Aux_TwinWidthI_MinorFree_twinWidth_components

open Aux_TwinWidthI_MinorFree_twinWidth_components in
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) :
    TwinWidthI.BoolWidth.TwinWidthLE G d ↔
      ∀ c : G.ConnectedComponent,
        letI : Fintype c.supp := Fintype.ofFinite c.supp
        letI : DecidableEq c.supp := Classical.decEq c.supp
        TwinWidthI.BoolWidth.TwinWidthLE (G.induce c.supp) d := by
  constructor
  · intro h c
    have hg := good_of_tw G d h
    have hr := good_restrict G d (Finset.subset_univ (sF c.supp)) _ hg
    rw [bot_restrict] at hr
    exact (sub_iff c.supp (instF := Fintype.ofFinite c.supp) (instD := Classical.decEq c.supp)
      G d).mpr hr
  · intro h
    have hg : ∀ c : G.ConnectedComponent, Good G d (⊥ : Finpartition (sF c.supp)) := fun c =>
      (sub_iff c.supp (instF := Fintype.ofFinite c.supp) (instD := Classical.decEq c.supp)
        G d).mp (h c)
    obtain ⟨N, Ps, h0, hl, hs, hd⟩ := tw_of_good G d (good_union G d hg)
    exact ⟨N, Ps, h0, hl, hs, hd⟩
