-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_298b1a86_18b6_4bc5_96f4_b68905059bb9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:29:36.737751+00:00
-- url     : https://prove2.me/submissions/33a7b729-691b-435a-95fe-e730234475d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_edge_bounded_extension

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by
  obtain ⟨K, hNK, hKdraw, hKbound⟩ :=
    WilliamsonShmoys.planar_graph_has_edge_bounded_extension N hNdraw hCard
  have hKN : K ≤ N := hMax K hNK hKdraw
  have hEq : K = N := le_antisymm hKN hNK
  rw [← hEq]
  exact hKbound