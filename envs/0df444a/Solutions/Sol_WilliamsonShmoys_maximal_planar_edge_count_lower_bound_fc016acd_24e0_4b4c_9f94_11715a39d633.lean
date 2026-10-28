-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_fc016acd_24e0_4b4c_9f94_11715a39d633
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:57:38.986758+00:00
-- url     : https://prove2.me/submissions/0e1b08d6-caf2-4c34-a341-28198999a297
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_drawing_supergraph_with_edge_count

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L -> L <= K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hCount⟩ :=
    WilliamsonShmoys.exists_planar_drawing_supergraph_with_edge_count K hK hCard
  have hLK : L <= K := hMax L hKL hL
  have hEq : L = K := le_antisymm hLK hKL
  rw [← hEq]
  omega