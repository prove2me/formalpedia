-- Prove2me | solution 1 for PathsTreesFlowers.Invariance.theorem_6_2_b
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:06:05.219811+00:00
-- url     : https://prove2.me/submissions/219fdb6d-24ef-41ad-8be3-749cd8e0df9c

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink
import Definitions.Def_PathsTreesFlowers_Invariance_Config



namespace PathsTreesFlowers.Invariance

section helpers
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}

lemma mem_outerSet_iff' (C : Config60 G M) (v : V) :
    v ∈ outerSet C ↔ ∃ i, partOf C.P v ∈ (C.J i).outer := by
  constructor
  · rintro (⟨_, h⟩ | h)
    · exact h
    · exact C.pseudo_outer (C.P.part v) (C.P.part_mem.2 (Finset.mem_univ v)) h
  · rintro ⟨i, hi⟩
    have hpos : 0 < (C.P.part v).card :=
      Finset.card_pos.2 ⟨v, C.P.mem_part (Finset.mem_univ v)⟩
    by_cases h1 : (C.P.part v).card = 1
    · exact Or.inl ⟨h1, i, hi⟩
    · exact Or.inr (by omega)

lemma not_inner_of_outer' (C : Config60 G M) {x : {U // U ∈ C.P.parts}} {i j : Fin C.n}
    (ho : x ∈ (C.J i).outer) (hi : x ∈ (C.J j).inner) : False := by
  by_cases h : i = j
  · subst h
    exact Finset.disjoint_left.1 (C.J i).disjoint_inner_outer hi ho
  · have hd := C.disjoint i j h
    have h1 : x ∈ (C.J i).verts := by rw [(C.J i).verts_eq]; exact Finset.mem_union_right _ ho
    have h2 : x ∈ (C.J j).verts := by rw [(C.J j).verts_eq]; exact Finset.mem_union_left _ hi
    exact Finset.disjoint_left.1 hd h1 h2

lemma inner_part_singleton' (C : Config60 G M) (v : V) {i : Fin C.n}
    (hi : partOf C.P v ∈ (C.J i).inner) : C.P.part v = {v} := by
  have hmem := C.P.mem_part (Finset.mem_univ v)
  by_contra hne
  have hpos : 0 < (C.P.part v).card := Finset.card_pos.2 ⟨v, hmem⟩
  have hcard : 1 < (C.P.part v).card := by
    by_contra hc
    have h1 : (C.P.part v).card = 1 := by omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h1
    rw [ha] at hmem hne
    have : v = a := by simpa using hmem
    subst this
    exact hne rfl
  obtain ⟨j, hj⟩ := C.pseudo_outer _ (C.P.part_mem.2 (Finset.mem_univ v)) hcard
  exact not_inner_of_outer' C hj hi

lemma inner_not_outer' (C : Config60 G M) {v : V} (hv : v ∈ innerSet C) : v ∉ outerSet C := by
  intro ho
  obtain ⟨i, hi⟩ := hv
  obtain ⟨j, hj⟩ := (mem_outerSet_iff' C v).1 ho
  exact not_inner_of_outer' C hj hi

lemma outer_adj' (C : Config60 G M) {u w : V} (hu : u ∈ outerSet C) (e : E)
    (he : G.ends e = s(u, w)) : w ∈ innerSet C ∨ C.P.part w = C.P.part u := by
  by_cases hpart : C.P.part w = C.P.part u
  · exact Or.inr hpart
  left
  obtain ⟨i, hi⟩ := (mem_outerSet_iff' C u).1 hu
  have hnd : ¬ ((G.ends e).map (partOf C.P)).IsDiag := by
    rw [he, Sym2.map_mk, Sym2.mk_isDiag_iff]
    intro h
    exact hpart (congrArg Subtype.val h).symm
  have hends : (shrink G C.P).ends ⟨e, hnd⟩ = s(partOf C.P u, partOf C.P w) := by
    show (G.ends e).map (partOf C.P) = _
    rw [he, Sym2.map_mk]
  rcases C.ordered_hungarian i (partOf C.P u) hi ⟨e, hnd⟩ (partOf C.P w) hends with
    h | ⟨h, hh, hw⟩
  · exact ⟨i, h⟩
  · rw [(C.J h).verts_eq, Finset.mem_union] at hw
    rcases hw with hw | hw
    · exact ⟨h, hw⟩
    · exfalso
      have hends' : (shrink G C.P).ends ⟨e, hnd⟩ = s(partOf C.P w, partOf C.P u) := by
        rw [hends, Sym2.eq_swap]
      rcases C.ordered_hungarian h (partOf C.P w) hw ⟨e, hnd⟩ (partOf C.P u) hends' with
        h' | ⟨h2, hh2, hu2⟩
      · exact not_inner_of_outer' C hi h'
      · have hd := C.disjoint i h2 (lt_trans hh2 hh).ne'
        have h1 : partOf C.P u ∈ (C.J i).verts := by
          rw [(C.J i).verts_eq]; exact Finset.mem_union_right _ hi
        exact Finset.disjoint_left.1 hd h1 hu2

lemma inner_adj' (C : Config60 G M) {v : V} (hv : v ∈ innerSet C) :
    ∃ u ∈ outerSet C, ∃ e : E, G.ends e = s(u, v) := by
  obtain ⟨i, hi⟩ := hv
  have hdeg := (C.J i).inner_degree _ hi
  have h2 : 0 < 2 := by norm_num
  rw [← hdeg] at h2
  obtain ⟨e, he⟩ := Finset.card_pos.1 h2
  rw [Finset.mem_filter] at he
  obtain ⟨he1, hmem⟩ := he
  obtain ⟨u', hu', w, hw, hends⟩ := (C.J i).edge_inner_outer e he1
  rw [hends] at hmem
  have hpv : partOf C.P v = u' := by
    rcases Sym2.mem_iff.1 hmem with h | h
    · exact h
    · exfalso
      rw [h] at hi
      exact not_inner_of_outer' C hw hi
  have hsing := inner_part_singleton' C v hi
  have key : ∀ x : V, partOf C.P x = partOf C.P v → x = v := by
    intro x hx
    have : C.P.part x = C.P.part v := congrArg Subtype.val hx
    have hxm : x ∈ C.P.part x := C.P.mem_part (Finset.mem_univ x)
    rw [this, hsing] at hxm
    simpa using hxm
  obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends e.1)
  have hab' : G.ends e.1 = s(a, b) := hab.symm
  have hends2 : s(partOf C.P a, partOf C.P b) = s(partOf C.P v, w) := by
    have : (shrink G C.P).ends e = (G.ends e.1).map (partOf C.P) := rfl
    rw [← hpv] at hends
    rw [← hends, this, hab', Sym2.map_mk]
  rw [hpv] at hends2
  rw [Sym2.eq_iff] at hends2
  rcases hends2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hav : a = v := key a (by rw [h1, hpv])
    have hbo : b ∈ outerSet C := (mem_outerSet_iff' C b).2 ⟨i, by rw [h2]; exact (hw)⟩
    refine ⟨b, hbo, e.1, ?_⟩
    rw [hab', hav, Sym2.eq_swap]
  · have hbv : b = v := key b (by rw [h2, hpv])
    have hao : a ∈ outerSet C := (mem_outerSet_iff' C a).2 ⟨i, by rw [h1]; exact (hw)⟩
    refine ⟨a, hao, e.1, ?_⟩
    rw [hab', hbv]

end helpers
theorem t62b_core {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (C : Config60 G M) :
    ∀ v : V, v ∈ innerSet C ↔ v ∉ outerSet C ∧ ∃ u ∈ outerSet C, ∃ e : E, G.ends e = s(u, v) := by
  intro v
  constructor
  · intro hv
    exact ⟨inner_not_outer' C hv, inner_adj' C hv⟩
  · rintro ⟨hno, u, hu, e, he⟩
    rcases outer_adj' C hu e he with h | h
    · exact h
    · exfalso
      apply hno
      obtain ⟨i, hi⟩ := (mem_outerSet_iff' C u).1 hu
      refine (mem_outerSet_iff' C v).2 ⟨i, ?_⟩
      have : partOf C.P v = partOf C.P u := Subtype.ext h
      rw [this]; exact hi

end PathsTreesFlowers.Invariance

open PathsTreesFlowers.Invariance


theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (C : Config60 G M) :
    ∀ v : V, v ∈ innerSet C ↔ v ∉ outerSet C ∧ ∃ u ∈ outerSet C, ∃ e : E, G.ends e = s(u, v) := by
  exact t62b_core G M C
