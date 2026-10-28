-- Prove2me | solution 2 for WilliamsonShmoys.planar_proper_supergraph_of_disconnected_planar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:35:38.715293+00:00
-- url     : https://prove2.me/submissions/30f57684-ef18-4496-a018-0dd0adccc483
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_adds_missing_edge_with_cardinality

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hDisconnected : ¬ P.Connected) :
    ∃ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧ P ≤ Q ∧ P ≠ Q := by
  obtain ⟨u, v, huv, hnot, hdraw⟩ :=
    WilliamsonShmoys.planar_drawing_adds_missing_edge_with_cardinality
      P hCard hP hDisconnected
  let E : SimpleGraph V :=
    SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))
  let Q : SimpleGraph V := P ⊔ E
  refine ⟨Q, ?_, le_sup_left, ?_⟩
  · simpa [Q, E] using hdraw
  · intro hEq
    apply hnot
    have hnew : E.Adj u v := by
      simp [E, huv]
    have hsup : Q.Adj u v := by
      change P.Adj u v ∨ E.Adj u v
      exact Or.inr hnew
    exact hEq.symm ▸ hsup