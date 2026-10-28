-- Prove2me | solution 1 for WilliamsonShmoys.connected_component_edge_bound_from_hypothesis
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:12:06.647418+00:00
-- url     : https://prove2.me/submissions/09d637cd-52df-40a6-a590-805993421392

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hS : ∀ S : Finset V, 3 ≤ S.card →
      (K.induce (↑S : Set V)).Connected →
      (K.induce (↑S : Set V)).edgeSet.ncard + 6 ≤ 3 * S.card)
    (C : K.ConnectedComponent)
    (hC : 3 ≤ C.supp.ncard) :
    (K.induce C.supp).edgeSet.ncard + 6 ≤ 3 * C.supp.ncard := by
  let hfinite : C.supp.Finite := Set.toFinite C.supp
  let S : Finset V := hfinite.toFinset
  have hS_eq : (↑S : Set V) = C.supp := hfinite.coe_toFinset
  have hcard : S.card = C.supp.ncard := by
    simpa [S] using (Set.ncard_eq_toFinset_card C.supp hfinite).symm
  have hlarge : 3 ≤ S.card := by rw [hcard]; exact hC
  have hconn : (K.induce (↑S : Set V)).Connected := by
    rw [hS_eq]
    exact C.connected_toSimpleGraph
  let e : (K.induce (↑S : Set V)) ≃g (K.induce C.supp) := {
    toEquiv := Equiv.setCongr hS_eq
    map_rel_iff' := by
      intro x y
      rfl
  }
  have hedge : (K.induce (↑S : Set V)).edgeSet.ncard =
      (K.induce C.supp).edgeSet.ncard :=
    Set.ncard_congr' e.mapEdgeSet
  rw [← hedge, ← hcard]
  exact hS S hlarge hconn