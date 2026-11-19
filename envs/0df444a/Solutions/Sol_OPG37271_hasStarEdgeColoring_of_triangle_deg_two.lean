-- Prove2me | solution 1 for OPG37271.hasStarEdgeColoring_of_triangle_deg_two
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:51:04.087065+00:00
-- url     : https://prove2.me/submissions/16a9cea9-f38f-4462-a10a-f80382c1223e

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
    convert hsub v using 1; congr 1; ext x; simp
  rw [Set.encard_coe_eq_coe_finsetCard] at h
  exact Nat.cast_le.mp h

theorem solution {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hsub : IsSubcubic G) (x y z : V)
    (hxz : G.Adj x z) (hyz : G.Adj y z) (hxy : G.Adj x y)
    (hz2 : (G.neighborSet z).encard ≤ 2)
    (hc' : HasStarEdgeColoring (G.deleteEdges {s(x, z)}) 7) :
    HasStarEdgeColoring G 7 := by
  classical
  refine OPG37271.hasStarEdgeColoring_of_dist_le_two_lt x z hxz hc' ?_
  let G' := G.deleteEdges {s(x, z)}
  have hG'le : G' ≤ G := SimpleGraph.deleteEdges_le {s(x, z)}
  have hsub' : IsSubcubic G' := fun w => le_trans (Set.encard_le_encard (SimpleGraph.neighborSet_mono hG'le w)) (hsub w)
  have hz_only : ∀ w : V, G'.Adj z w → w = y := by
    intro w hzw
    have hzwG : w ∈ G.neighborFinset z := (SimpleGraph.mem_neighborFinset G z w).mpr (hG'le hzw)
    have hzxG : x ∈ G.neighborFinset z := (SimpleGraph.mem_neighborFinset G z x).mpr hxz.symm
    have hzyG : y ∈ G.neighborFinset z := (SimpleGraph.mem_neighborFinset G z y).mpr hyz.symm
    have hz_card : (G.neighborFinset z).card ≤ 2 := by
      have h : ((G.neighborFinset z : Set V)).encard ≤ 2 := by
        convert hz2 using 1; congr 1; ext a; simp
      rw [Set.encard_coe_eq_coe_finsetCard] at h
      exact Nat.cast_le.mp h
    have hsub2 : {x, y} ⊆ G.neighborFinset z := by
      intro a ha
      rw [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> assumption
    have hxy_ne : x ≠ y := hxy.ne
    have hcard2 : ({x, y} : Finset V).card = 2 := Finset.card_pair hxy_ne
    have heq : {x, y} = G.neighborFinset z := Finset.eq_of_subset_of_card_le hsub2 (by omega)
    have hw_in : w ∈ ({x, y} : Finset V) := heq ▸ hzwG
    rw [Finset.mem_insert, Finset.mem_singleton] at hw_in
    rcases hw_in with rfl | rfl
    · exfalso
      apply (SimpleGraph.deleteEdges_adj.mp hzw).2
      simp [Sym2.eq_swap]
    · rfl
  have hx_le2 : (G'.neighborFinset x).card ≤ 2 := by
    have hle : G'.neighborFinset x ⊆ (G.neighborFinset x).erase z := by
      intro w hw
      rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
      rw [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj] at hw
      refine ⟨?_, hw.1⟩
      intro hwz; apply hw.2; subst hwz; simp
    have hcard := Finset.card_le_card hle
    rw [Finset.card_erase_of_mem ((SimpleGraph.mem_neighborFinset G x z).mpr hxz)] at hcard
    exact le_trans hcard (by have := card_neighborFinset_le_of_subcubic hsub x; omega)
  have hy_mem_x : y ∈ G'.neighborFinset x := by
    rw [SimpleGraph.mem_neighborFinset]
    refine SimpleGraph.deleteEdges_adj.mpr ⟨hxy, ?_⟩
    intro heq; rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
    rcases heq with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hyz.ne h2
    · exact hxz.ne h1
  have hex_w : ∃ w₀ : V, ∀ w : V, G'.Adj x w → w = y ∨ w = w₀ := by
    have hcard_er : ((G'.neighborFinset x).erase y).card ≤ 1 := by
      rw [Finset.card_erase_of_mem hy_mem_x]
      omega
    by_cases h0 : ((G'.neighborFinset x).erase y).card = 0
    · refine ⟨y, fun w hxw => Or.inl ?_⟩
      by_contra hne
      have hmem : w ∈ (G'.neighborFinset x).erase y :=
        Finset.mem_erase.mpr ⟨hne, (SimpleGraph.mem_neighborFinset G' x w).mpr hxw⟩
      rw [Finset.card_eq_zero] at h0
      rw [h0] at hmem
      exact Finset.notMem_empty w hmem
    · have h1 : ((G'.neighborFinset x).erase y).card = 1 := by omega
      rcases Finset.card_eq_one.mp h1 with ⟨w₀, hw₀⟩
      refine ⟨w₀, fun w hxw => ?_⟩
      by_cases hwy : w = y
      · exact Or.inl hwy
      · right
        have hmem : w ∈ (G'.neighborFinset x).erase y :=
          Finset.mem_erase.mpr ⟨hwy, (SimpleGraph.mem_neighborFinset G' x w).mpr hxw⟩
        rw [hw₀, Finset.mem_singleton] at hmem
        exact hmem
  rcases hex_w with ⟨w₀, hw₀⟩
  let E (a : V) : Finset (Sym2 V) := (G'.neighborFinset a).image fun b => s(a, b)
  have hE_card : ∀ a : V, (E a).card ≤ 3 := fun a =>
    le_trans Finset.card_image_le (card_neighborFinset_le_of_subcubic hsub' a)
  refine ⟨E y ∪ E w₀, ?_, ?_⟩
  · calc (E y ∪ E w₀).card ≤ (E y).card + (E w₀).card := Finset.card_union_le _ _
      _ ≤ 3 + 3 := Nat.add_le_add (hE_card y) (hE_card w₀)
      _ < 7 := by omega
  · intro a b hab hne hdist
    have hab' : G'.Adj a b := SimpleGraph.deleteEdges_adj.mpr ⟨hab, hne⟩
    have hmem_E : ∀ u : V, (a = u ∨ b = u) → s(a, b) ∈ E u := by
      intro u hu
      rcases hu with rfl | rfl
      · exact Finset.mem_image.mpr ⟨b, (SimpleGraph.mem_neighborFinset G' a b).mpr hab', rfl⟩
      · exact Finset.mem_image.mpr ⟨a, (SimpleGraph.mem_neighborFinset G' b a).mpr hab'.symm, Sym2.eq_swap⟩
    have hfrom_x : ∀ u : V, G'.Adj x u → (a = u ∨ b = u) → s(a, b) ∈ E y ∪ E w₀ := by
      intro u hxu hau
      rcases hw₀ u hxu with huy | huw
      · rw [huy] at hau; exact Finset.mem_union_left _ (hmem_E y hau)
      · rw [huw] at hau; exact Finset.mem_union_right _ (hmem_E w₀ hau)
    have hfrom_z : ∀ u : V, G'.Adj z u → (a = u ∨ b = u) → s(a, b) ∈ E y ∪ E w₀ := by
      intro u hzu hau
      rw [hz_only u hzu] at hau
      exact Finset.mem_union_left _ (hmem_E y hau)
    have hadj_del : ∀ u v' : V, G.Adj u v' → s(u, v') ≠ s(x, z) → G'.Adj u v' :=
      fun u v' huv' hne' => SimpleGraph.deleteEdges_adj.mpr ⟨huv', hne'⟩
    rcases hdist with rfl | rfl | rfl | rfl | hxa | hza | hxb | hzb
    · exact hfrom_x b hab' (Or.inr rfl)
    · exact hfrom_z b hab' (Or.inr rfl)
    · exact hfrom_x a hab'.symm (Or.inl rfl)
    · exact hfrom_z a hab'.symm (Or.inl rfl)
    · by_cases haz : a = z
      · subst haz; exact hfrom_z b hab' (Or.inr rfl)
      · exact hfrom_x a (hadj_del x a hxa (by intro heq; rw [Sym2.eq_iff] at heq; rcases heq with ⟨_, h2⟩ | ⟨h1, _⟩; exact haz h2; exact hxz.ne h1)) (Or.inl rfl)
    · by_cases hax : a = x
      · subst hax; exact hfrom_x b hab' (Or.inr rfl)
      · exact hfrom_z a (hadj_del z a hza (by intro heq; rw [Sym2.eq_iff] at heq; rcases heq with ⟨h1, h2⟩ | ⟨_, h2⟩; exact hxz.ne h1.symm; exact hax h2)) (Or.inl rfl)
    · by_cases hbz : b = z
      · subst hbz; exact hfrom_z a hab'.symm (Or.inl rfl)
      · exact hfrom_x b (hadj_del x b hxb (by intro heq; rw [Sym2.eq_iff] at heq; rcases heq with ⟨_, h2⟩ | ⟨h1, _⟩; exact hbz h2; exact hxz.ne h1)) (Or.inr rfl)
    · by_cases hbx : b = x
      · subst hbx; exact hfrom_x a hab'.symm (Or.inl rfl)
      · exact hfrom_z b (hadj_del z b hzb (by intro heq; rw [Sym2.eq_iff] at heq; rcases heq with ⟨h1, h2⟩ | ⟨_, h2⟩; exact hxz.ne h1.symm; exact hbx h2)) (Or.inr rfl)
