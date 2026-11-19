-- Prove2me | solution 1 for OPG37271.hasStarEdgeColoring_of_adj_deg_le_two
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:48:09.911858+00:00
-- url     : https://prove2.me/submissions/7fc877cd-1f5e-46b4-9433-d2788a5b7b9b

import Definitions.Def_opg37271_star_edge_coloring
import Theorems.Thm_OPG37271_hasStarEdgeColoring_of_dist_le_two_lt
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Finset.Card

set_option autoImplicit false

open OPG37271

universe u

private lemma card_neighborFinset_le_of_subcubic {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hsub : IsSubcubic G) (v : V) :
    (G.neighborFinset v).card ≤ 3 := by
  have h : ((G.neighborFinset v : Set V)).encard ≤ 3 := by
    convert hsub v using 1
    congr 1
    ext x
    simp
  rw [Set.encard_coe_eq_coe_finsetCard] at h
  exact Nat.cast_le.mp h

theorem solution {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hsub : IsSubcubic G) (u v : V) (huv : G.Adj u v)
    (hu2 : (G.neighborSet u).encard ≤ 2) (hv2 : (G.neighborSet v).encard ≤ 2)
    (hc' : HasStarEdgeColoring (G.deleteEdges {s(u, v)}) 7) :
    HasStarEdgeColoring G 7 := by
  classical
  refine OPG37271.hasStarEdgeColoring_of_dist_le_two_lt u v huv hc' ?_
  let G' := G.deleteEdges {s(u, v)}
  have hG'le : G' ≤ G := SimpleGraph.deleteEdges_le {s(u, v)}
  have hsub' : IsSubcubic G' := fun w => le_trans (Set.encard_le_encard (SimpleGraph.neighborSet_mono hG'le w)) (hsub w)
  have hdeg_del : ∀ a b : V, G.Adj a b → (G.neighborSet a).encard ≤ 2 →
      ((G.deleteEdges {s(a, b)}).neighborFinset a).card ≤ 1 := by
    intro a b hab ha2
    have ha_fin : (G.neighborFinset a).card ≤ 2 := by
      have h : ((G.neighborFinset a : Set V)).encard ≤ 2 := by
        convert ha2 using 1; congr 1; ext x; simp
      rw [Set.encard_coe_eq_coe_finsetCard] at h
      exact Nat.cast_le.mp h
    have hle : (G.deleteEdges {s(a, b)}).neighborFinset a ⊆ (G.neighborFinset a).erase b := by
      intro w hw
      rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
      rw [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj] at hw
      refine ⟨?_, hw.1⟩
      intro hwa; apply hw.2; subst hwa; simp
    have hcard := Finset.card_le_card hle
    rw [Finset.card_erase_of_mem ((SimpleGraph.mem_neighborFinset G a b).mpr hab)] at hcard
    omega
  have hu1 : (G'.neighborFinset u).card ≤ 1 := hdeg_del u v huv hu2
  have hv1 : (G'.neighborFinset v).card ≤ 1 := by
    have hle : G'.neighborFinset v ⊆ (G.deleteEdges {s(v, u)}).neighborFinset v := by
      intro w hw; simpa [G', Sym2.eq_swap] using hw
    exact le_trans (Finset.card_le_card hle) (hdeg_del v u huv.symm hv2)
  let S (a : V) : Finset (Sym2 V) :=
    (G'.neighborFinset a).biUnion fun w => (G'.neighborFinset w).image fun z => s(w, z)
  have hS_bound : ∀ a : V, (G'.neighborFinset a).card ≤ 1 → (S a).card ≤ 3 := by
    intro a ha
    calc (S a).card
        ≤ ∑ w ∈ G'.neighborFinset a, ((G'.neighborFinset w).image fun z => s(w, z)).card := Finset.card_biUnion_le
      _ ≤ ∑ w ∈ G'.neighborFinset a, (G'.neighborFinset w).card := Finset.sum_le_sum fun w _ => Finset.card_image_le
      _ ≤ ∑ _w ∈ G'.neighborFinset a, 3 := Finset.sum_le_sum fun w _ => card_neighborFinset_le_of_subcubic hsub' w
      _ = (G'.neighborFinset a).card * 3 := by simp
      _ ≤ 1 * 3 := Nat.mul_le_mul_right 3 ha
      _ = 3 := rfl
  refine ⟨S u ∪ S v, ?_, ?_⟩
  · calc (S u ∪ S v).card ≤ (S u).card + (S v).card := Finset.card_union_le _ _
      _ ≤ 3 + 3 := Nat.add_le_add (hS_bound u hu1) (hS_bound v hv1)
      _ < 7 := by omega
  · intro x y hxy hne hdist
    have hxy' : G'.Adj x y := SimpleGraph.deleteEdges_adj.mpr ⟨hxy, hne⟩
    have hmem_S : ∀ a : V, (x = a ∨ y = a ∨ G'.Adj a x ∨ G'.Adj a y) → s(x, y) ∈ S a := by
      intro a ha
      rw [Finset.mem_biUnion]
      rcases ha with rfl | rfl | hax | hay
      · exact ⟨y, (SimpleGraph.mem_neighborFinset G' x y).mpr hxy', Finset.mem_image.mpr ⟨x, (SimpleGraph.mem_neighborFinset G' y x).mpr hxy'.symm, Sym2.eq_swap⟩⟩
      · exact ⟨x, (SimpleGraph.mem_neighborFinset G' y x).mpr hxy'.symm, Finset.mem_image.mpr ⟨y, (SimpleGraph.mem_neighborFinset G' x y).mpr hxy', rfl⟩⟩
      · exact ⟨x, (SimpleGraph.mem_neighborFinset G' a x).mpr hax, Finset.mem_image.mpr ⟨y, (SimpleGraph.mem_neighborFinset G' x y).mpr hxy', rfl⟩⟩
      · exact ⟨y, (SimpleGraph.mem_neighborFinset G' a y).mpr hay, Finset.mem_image.mpr ⟨x, (SimpleGraph.mem_neighborFinset G' y x).mpr hxy'.symm, Sym2.eq_swap⟩⟩
    rw [Finset.mem_union]
    by_cases hxu : x = u; · exact Or.inl (hmem_S u (Or.inl hxu))
    by_cases hxv : x = v; · exact Or.inr (hmem_S v (Or.inl hxv))
    by_cases hyu : y = u; · exact Or.inl (hmem_S u (Or.inr (Or.inl hyu)))
    by_cases hyv : y = v; · exact Or.inr (hmem_S v (Or.inr (Or.inl hyv)))
    rcases hdist with rfl | rfl | rfl | rfl | hux | hvx | huy | hvy
    · exact absurd rfl hxu
    · exact absurd rfl hxv
    · exact absurd rfl hyu
    · exact absurd rfl hyv
    · refine Or.inl (hmem_S u (Or.inr (Or.inr (Or.inl (SimpleGraph.deleteEdges_adj.mpr ⟨hux, ?_⟩)))))
      intro heq; rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
      rcases heq with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact hxv h2
      · exact huv.ne h1
    · refine Or.inr (hmem_S v (Or.inr (Or.inr (Or.inl (SimpleGraph.deleteEdges_adj.mpr ⟨hvx, ?_⟩)))))
      intro heq; rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
      rcases heq with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact huv.ne h1.symm
      · exact hxu h2
    · refine Or.inl (hmem_S u (Or.inr (Or.inr (Or.inr (SimpleGraph.deleteEdges_adj.mpr ⟨huy, ?_⟩)))))
      intro heq; rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
      rcases heq with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact hyv h2
      · exact huv.ne h1
    · refine Or.inr (hmem_S v (Or.inr (Or.inr (Or.inr (SimpleGraph.deleteEdges_adj.mpr ⟨hvy, ?_⟩)))))
      intro heq; rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
      rcases heq with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact huv.ne h1.symm
      · exact hyu h2
