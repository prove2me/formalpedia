-- Prove2me | solution 1 for WilliamsonShmoys.planar_proper_supergraph_of_disconnected_planar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:23:06.539155+00:00
-- url     : https://prove2.me/submissions/4172dfb1-b29a-4398-984e-3de56145643e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_adds_an_edge_between_components

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
    WilliamsonShmoys.planar_drawing_adds_an_edge_between_components P hP hDisconnected
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