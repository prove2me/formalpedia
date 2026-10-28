-- Prove2me | solution 1 for WilliamsonShmoys.component_induced_edge_ncard_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T22:41:47.577058+00:00
-- url     : https://prove2.me/submissions/4e75971f-e94a-41f4-b104-fb6f17499997

import Mathlib
open SimpleGraph in
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) :
    (∑ C : K.ConnectedComponent, (K.induce C.supp).edgeSet.ncard) =
      K.edgeSet.ncard := by
  classical
  let f : Sym2 V → K.ConnectedComponent := fun e => K.connectedComponentMk e.out.1
  have hmem : ∀ e ∈ K.edgeSet, ∀ v ∈ e, K.connectedComponentMk v = f e := by
    intro e he v hv
    have h1 : e.out.1 ∈ e := Sym2.out_fst_mem e
    induction e using Sym2.ind with
    | h a b =>
      have hab : K.connectedComponentMk a = K.connectedComponentMk b :=
        ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable he)
      rcases Sym2.mem_iff.mp hv with rfl | rfl <;>
        rcases Sym2.mem_iff.mp h1 with h | h <;> simp only [f, h, hab]
  have himg : ∀ C : K.ConnectedComponent,
      Sym2.map Subtype.val '' (K.induce C.supp).edgeSet = {e ∈ K.edgeSet | f e = C} := by
    intro C
    ext e
    constructor
    · rintro ⟨e', he', rfl⟩
      induction e' using Sym2.ind with
      | h a b =>
        have hab : K.Adj a.1 b.1 := he'
        refine ⟨hab, ?_⟩
        rw [← hmem _ hab a.1 (by simp)]
        exact a.2
    · intro ⟨he, hfe⟩
      induction e using Sym2.ind with
      | h a b =>
        have ha : a ∈ C.supp := by
          rw [ConnectedComponent.mem_supp_iff, hmem _ he a (by simp), hfe]
        have hb : b ∈ C.supp := by
          rw [ConnectedComponent.mem_supp_iff, hmem _ he b (by simp), hfe]
        exact ⟨s(⟨a, ha⟩, ⟨b, hb⟩), he, rfl⟩
  have hcard : ∀ C : K.ConnectedComponent,
      (K.induce C.supp).edgeSet.ncard = {e ∈ K.edgeSet | f e = C}.ncard := by
    intro C
    rw [← himg C, Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
  simp_rw [hcard]
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset,
    Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr (by ext; simp) fun C _ => ?_
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp
