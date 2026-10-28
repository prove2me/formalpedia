-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_adds_missing_edge_with_cardinality
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:43:22.838674+00:00
-- url     : https://prove2.me/submissions/ac30c293-c140-49c4-a204-17bd4d862926
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_disconnected_pair
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connects_distinct_components

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hDisconnected : ¬ P.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ P.Adj u v ∧
      WilliamsonShmoys.HasPlanarDrawingOn
        (P ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))) := by
  obtain ⟨u, v, huv, hnotadj, hseparate⟩ :=
    WilliamsonShmoys.planar_disconnected_pair P hCard hDisconnected
  exact ⟨u, v, huv, hnotadj,
    WilliamsonShmoys.planar_drawing_connects_distinct_components P hP huv hseparate⟩