-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_induced_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:31:42.753966+00:00
-- url     : https://prove2.me/submissions/b809f995-dceb-4670-9211-38c95c01722a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_edge_bound_for_finite_simple_graph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (C : Finset V)
    (hconn : (G.induce (fun v => v ∈ C)).Connected)
    (hcard : 3 ≤ C.card) :
    (G.induce (fun v => v ∈ C)).edgeSet.ncard + 6 ≤ 3 * C.card := by
  classical
  letI : Fintype {v : V // v ∈ C} := Finset.Subtype.fintype C
  have hcard_eq : Fintype.card {v : V // v ∈ C} = C.card := by
    change Fintype.card (↑C) = C.card
    exact Fintype.card_coe C
  have hdraw : WilliamsonShmoys.HasPlanarDrawingOn (G.induce (fun v => v ∈ C)) := by
    rcases hG with ⟨p, arc, hp, hedge, hcross⟩
    refine ⟨(fun w : {v : V // v ∈ C} => p w.1),
      (fun u v t => arc u.1 v.1 t), ?_, ?_, ?_⟩
    · intro u v huv
      apply Subtype.ext
      apply hp
      exact huv
    · intro u v huv hadj
      have hval : u.1 < v.1 := huv
      have hadj' : G.Adj u.1 v.1 := SimpleGraph.induce_adj.mp hadj
      obtain ⟨hc, hi, h0, h1, hn⟩ := hedge u.1 v.1 hval hadj'
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa using hc
      · simpa using hi
      · simpa using h0
      · simpa using h1
      · intro t ht w
        exact hn t ht w.1
    · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq
      have hne' : (u.1, v.1) ≠ (x.1, y.1) := by
        intro hval
        apply hne
        exact Prod.ext (Subtype.ext (congrArg Prod.fst hval))
          (Subtype.ext (congrArg Prod.snd hval))
      exact hcross u.1 v.1 x.1 y.1 huv hxy
        (SimpleGraph.induce_adj.mp hadj₁) (SimpleGraph.induce_adj.mp hadj₂)
        hne' t ht s hs (by simpa using heq)
  have hcard' : 3 ≤ Fintype.card {v : V // v ∈ C} := by
    rw [hcard_eq]
    exact hcard
  have hb := @WilliamsonShmoys.planar_drawing_euler_edge_bound_for_finite_simple_graph
    {v : V // v ∈ C} (Finset.Subtype.fintype C) inferInstance
    (G.induce (fun v => v ∈ C)) hdraw hcard'
  calc
    (G.induce (fun v => v ∈ C)).edgeSet.ncard + 6 ≤
        3 * Fintype.card {v : V // v ∈ C} := hb
    _ = 3 * C.card := by rw [hcard_eq]
