-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_of_component_bounds__p2m_dad39d86_4ed1_4b9b_930d_705a080f17ad_a4
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T06:29:16.227729+00:00
-- url     : https://prove2.me/submissions/d39672da-5e3a-4799-904e-223290255c2a

import Mathlib

namespace WSComp

lemma arith {ι : Type} (S : Finset ι) (e s : ι → ℕ) (hs : ∀ i ∈ S, 1 ≤ s i)
    (h : ∀ i ∈ S, (3 ≤ s i → e i + 6 ≤ 3 * s i) ∧ (s i < 3 → e i ≤ 1))
    (h3 : 3 ≤ ∑ i ∈ S, s i) : ∑ i ∈ S, e i + 6 ≤ 3 * ∑ i ∈ S, s i := by
  classical
  by_cases hex : ∃ i ∈ S, 3 ≤ s i
  · obtain ⟨i, hiS, hi⟩ := hex
    have hle : ∀ j ∈ S, e j ≤ 3 * s j := by
      intro j hj
      by_cases hj3 : 3 ≤ s j
      · have := (h j hj).1 hj3; omega
      · have := (h j hj).2 (by omega); have := hs j hj; omega
    rw [← Finset.add_sum_erase S e hiS, ← Finset.add_sum_erase S s hiS]
    have h1 : ∑ j ∈ S.erase i, e j ≤ ∑ j ∈ S.erase i, 3 * s j :=
      Finset.sum_le_sum (fun j hj => hle j (Finset.mem_of_mem_erase hj))
    rw [← Finset.mul_sum] at h1
    have := (h i hiS).1 hi
    omega
  · push_neg at hex
    have hle : ∀ j ∈ S, e j ≤ s j := by
      intro j hj
      have := (h j hj).2 (hex j hj); have := hs j hj; omega
    have := Finset.sum_le_sum hle
    omega

variable {V : Type} [Fintype V]

open Classical in
/-- the component of an edge -/
noncomputable def ecomp (L : SimpleGraph V) (e : Sym2 V) : L.ConnectedComponent :=
  L.connectedComponentMk e.out.1

lemma ecomp_eq (L : SimpleGraph V) {e : Sym2 V} (he : e ∈ L.edgeSet) {v : V} (hv : v ∈ e) :
    L.connectedComponentMk v = ecomp L e := by
  classical
  unfold ecomp
  have hm := Sym2.out_fst_mem e
  induction e using Sym2.ind with
  | h a b =>
    have hab : L.Adj a b := he
    have hr : L.Reachable a b := hab.reachable
    rw [Sym2.mem_iff] at hv hm
    rw [SimpleGraph.ConnectedComponent.eq]
    have key : ∀ x y : V, (x = a ∨ x = b) → (y = a ∨ y = b) → L.Reachable x y := by
      intro x y hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact SimpleGraph.Reachable.refl _
      · exact hr
      · exact hr.symm
      · exact SimpleGraph.Reachable.refl _
    exact key _ _ hv hm

open Classical in
lemma fiber_card (L : SimpleGraph V) (C : L.ConnectedComponent) [Fintype L.edgeSet] :
    ((L.edgeFinset).filter (fun e => ecomp L e = C)).card = C.toSimpleGraph.edgeSet.ncard := by
  classical
  symm
  have : ((L.edgeFinset).filter (fun e => ecomp L e = C) : Set (Sym2 V)).ncard
      = ((L.edgeFinset).filter (fun e => ecomp L e = C)).card := Set.ncard_coe_finset _
  rw [← this]
  apply Set.ncard_congr (fun (e : Sym2 C) _ => Sym2.map Subtype.val e)
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
      have hab : C.toSimpleGraph.Adj a b := he
      have hab' : L.Adj a.1 b.1 := by
        simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using hab
      simp only [Finset.coe_filter, SimpleGraph.mem_edgeFinset, Set.mem_setOf_eq, Sym2.map_pair_eq]
      refine ⟨hab', ?_⟩
      rw [← ecomp_eq L hab' (v := a.1) (by simp)]
      exact a.2
  · intro a b _ _ h
    exact Sym2.map.injective Subtype.val_injective h
  · intro e he
    simp only [Finset.coe_filter, SimpleGraph.mem_edgeFinset, Set.mem_setOf_eq] at he
    obtain ⟨he1, he2⟩ := he
    induction e using Sym2.ind with
    | h a b =>
      have ha : a ∈ C.supp := by
        show L.connectedComponentMk a = C
        rw [ecomp_eq L he1 (v := a) (by simp)]; exact he2
      have hb : b ∈ C.supp := by
        show L.connectedComponentMk b = C
        rw [ecomp_eq L he1 (v := b) (by simp)]; exact he2
      refine ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, by simp⟩
      show C.toSimpleGraph.Adj ⟨a, ha⟩ ⟨b, hb⟩
      simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using he1

lemma edge_sum (L : SimpleGraph V) :
    L.edgeSet.ncard = ∑ C : L.ConnectedComponent, C.toSimpleGraph.edgeSet.ncard := by
  classical
  have h1 : L.edgeSet.ncard = L.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']; congr
  rw [h1, Finset.card_eq_sum_card_fiberwise (f := ecomp L) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr (by convert rfl) (fun C _ => ?_)
  exact fiber_card L C

lemma vert_sum (L : SimpleGraph V) :
    Fintype.card V = ∑ C : L.ConnectedComponent, C.supp.ncard := by
  classical
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := L.connectedComponentMk)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr (by convert rfl) (fun C _ => ?_)
  rw [← Set.ncard_coe_finset]
  congr 1
  ext v
  simp [SimpleGraph.ConnectedComponent.mem_supp_iff]

end WSComp

theorem solution
    {V : Type} [Fintype V]
    (L : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hcomp : ∀ C : L.ConnectedComponent,
      (3 ≤ C.supp.ncard →
        C.toSimpleGraph.edgeSet.ncard + 6 ≤ 3 * C.supp.ncard) ∧
      (C.supp.ncard < 3 → C.toSimpleGraph.edgeSet.ncard ≤ 1)) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  classical
  rw [WSComp.edge_sum L, WSComp.vert_sum L]
  rw [WSComp.vert_sum L] at hcard
  refine WSComp.arith _ (fun C : L.ConnectedComponent => C.toSimpleGraph.edgeSet.ncard)
    (fun C : L.ConnectedComponent => C.supp.ncard) ?_ (fun C _ => hcomp C) hcard
  intro C _
  have : C.supp.Nonempty := C.nonempty_supp
  have := Set.ncard_pos (Set.toFinite C.supp) |>.2 this
  omega
