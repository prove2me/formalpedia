-- Prove2me | solution 1 for ShortestConnection.Principles.construction_acyclic_card_components
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:05:51.61577+00:00
-- url     : https://prove2.me/submissions/76005841-f2f1-40a6-a4b5-cd2f25464efc

import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

open SimpleGraph

/-- Reachability in `G ⊔ edge u v`: starting from `x`, either `x` already reaches the target
in `G`, or `x` reaches one of the endpoints `u`, `v` in `G`. -/
theorem aux_scacc_reach {V : Type*} (G : SimpleGraph V) (u v x y : V)
    (h : (G ⊔ edge u v).Reachable x y) :
    G.Reachable x y ∨ G.Reachable x u ∨ G.Reachable x v := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl (Reachable.refl x)
  | tail _ hbc ih =>
    rename_i b c
    rw [sup_adj, edge_adj] at hbc
    rcases hbc with hbc | ⟨hbc, _⟩
    · rcases ih with ih | ih | ih
      · exact Or.inl (ih.trans hbc.reachable)
      · exact Or.inr (Or.inl ih)
      · exact Or.inr (Or.inr ih)
    · rcases ih with ih | ih | ih
      · rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ih)
        · exact Or.inr (Or.inr ih)
      · exact Or.inr (Or.inl ih)
      · exact Or.inr (Or.inr ih)

/-- Adding an edge between two mutually unreachable vertices lowers the number of connected
components by one. -/
theorem aux_scacc_card {V : Type*} [Finite V] (G : SimpleGraph V) {u v : V}
    (h : ¬ G.Reachable u v) :
    Nat.card (G ⊔ edge u v).ConnectedComponent + 1 = Nat.card G.ConnectedComponent := by
  classical
  have huv : u ≠ v := by
    rintro rfl
    exact h (Reachable.refl u)
  have hle : G ≤ G ⊔ edge u v := le_sup_left
  have hadj : (G ⊔ edge u v).Adj u v := by
    rw [sup_adj, edge_adj]
    exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩
  have hne : G.connectedComponentMk u ≠ G.connectedComponentMk v := by
    rw [Ne, ConnectedComponent.eq]
    exact h
  let g : {c : G.ConnectedComponent // c ≠ G.connectedComponentMk v} →
      (G ⊔ edge u v).ConnectedComponent := fun c => c.1.map (Hom.ofLE hle)
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨c1, hc1⟩ ⟨c2, hc2⟩ heq
      induction c1 using ConnectedComponent.ind with
      | h x =>
      induction c2 using ConnectedComponent.ind with
      | h y =>
      simp only [g, ConnectedComponent.map_mk, Hom.coe_ofLE, id_eq, ConnectedComponent.eq] at heq
      rw [Ne, ConnectedComponent.eq] at hc1 hc2
      apply Subtype.ext
      simp only [ConnectedComponent.eq]
      rcases aux_scacc_reach G u v x y heq with h1 | h1 | h1
      · exact h1
      · rcases aux_scacc_reach G u v y x heq.symm with h2 | h2 | h2
        · exact h2.symm
        · exact h1.trans h2.symm
        · exact absurd h2 hc2
      · exact absurd h1 hc1
    · intro c'
      induction c' using ConnectedComponent.ind with
      | h x =>
      by_cases hx : G.connectedComponentMk x = G.connectedComponentMk v
      · refine ⟨⟨G.connectedComponentMk u, hne⟩, ?_⟩
        simp only [g, ConnectedComponent.map_mk, Hom.coe_ofLE, id_eq, ConnectedComponent.eq]
        rw [ConnectedComponent.eq] at hx
        exact hadj.reachable.trans (hx.symm.mono hle)
      · refine ⟨⟨G.connectedComponentMk x, hx⟩, ?_⟩
        simp only [g, ConnectedComponent.map_mk, Hom.coe_ofLE, id_eq]
  rw [← Nat.card_eq_of_bijective g hg, ← Nat.card_congr (Equiv.optionSubtypeNe
    (G.connectedComponentMk v)), Finite.card_option]

theorem aux_scacc_bot_card {V : Type*} [Fintype V] :
    Nat.card (⊥ : SimpleGraph V).ConnectedComponent = Fintype.card V := by
  rw [← Nat.card_eq_fintype_card]
  symm
  apply Nat.card_eq_of_bijective (fun x : V => (⊥ : SimpleGraph V).connectedComponentMk x)
  constructor
  · intro x y hxy
    simpa [ConnectedComponent.eq, reachable_bot] using hxy
  · intro c
    induction c using ConnectedComponent.ind with
    | h x => exact ⟨x, rfl⟩

theorem aux_scacc_insert {V : Type*} [DecidableEq V] (F : Finset (Sym2 V)) (a b : V) :
    linkGraph (insert s(a, b) F) = linkGraph F ⊔ edge a b := by
  ext x y
  simp only [linkGraph, edge, sup_adj, fromEdgeSet_adj, Finset.coe_insert, Set.mem_insert_iff,
    Finset.mem_coe, Set.mem_singleton_iff]
  tauto

/-- Every application of P1 or P2 joins two terminals that are not yet connected. -/
theorem aux_scacc_app {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) (F : Finset (Sym2 V))
    (e : Sym2 V) (h : IsApplication G w F e) :
    ∃ a b : V, e = s(a, b) ∧ ¬ (linkGraph F).Reachable a b := by
  rcases h with ⟨t, n, hiso, hG, he, -⟩ | ⟨u, n, -, hnr, -, he, -⟩
  · refine ⟨t, n, he, ?_⟩
    rintro ⟨p⟩
    cases p with
    | nil => exact hG.ne rfl
    | cons hadj _ => exact hiso _ hadj
  · exact ⟨u, n, he, hnr⟩

theorem aux_scacc_main {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (l : List (Sym2 V)) (hl : IsConstruction G w l) :
    (linkGraph l.toFinset).IsAcyclic ∧
      Nat.card (linkGraph l.toFinset).ConnectedComponent = Fintype.card V - l.length := by
  induction l using List.reverseRecOn with
  | nil =>
    simp only [List.toFinset_nil, List.length_nil, Nat.sub_zero]
    have h0 : linkGraph (∅ : Finset (Sym2 V)) = ⊥ := by
      simp [linkGraph]
    rw [h0]
    exact ⟨isAcyclic_bot, aux_scacc_bot_card⟩
  | append_singleton l e ih =>
    have hl' : IsConstruction G w l := by
      intro i hi
      have hi' : i < (l ++ [e]).length := by simp; omega
      have := hl i hi'
      rwa [List.take_append_of_le_length hi.le, List.getElem_append_left hi] at this
    have happ : IsApplication G w l.toFinset e := by
      have hi' : l.length < (l ++ [e]).length := by simp
      have := hl l.length hi'
      rw [List.take_left' rfl, List.getElem_concat_length rfl] at this
      exact this
    obtain ⟨hac, hcard⟩ := ih hl'
    obtain ⟨a, b, rfl, hnr⟩ := aux_scacc_app G w _ _ happ
    have hfs : (l ++ [s(a, b)]).toFinset = insert s(a, b) l.toFinset := by
      rw [List.toFinset_append]
      ext x
      simp [or_comm]
    rw [hfs, aux_scacc_insert]
    refine ⟨hac.sup_edge_of_not_reachable hnr, ?_⟩
    have := aux_scacc_card (linkGraph l.toFinset) hnr
    rw [List.length_append, List.length_singleton]
    omega

end ShortestConnection.Principles

open ShortestConnection.Principles

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (l : List (Sym2 V)) (hl : IsConstruction G w l) :
    (linkGraph l.toFinset).IsAcyclic ∧
      Nat.card (linkGraph l.toFinset).ConnectedComponent = Fintype.card V - l.length :=
  aux_scacc_main G w l hl
