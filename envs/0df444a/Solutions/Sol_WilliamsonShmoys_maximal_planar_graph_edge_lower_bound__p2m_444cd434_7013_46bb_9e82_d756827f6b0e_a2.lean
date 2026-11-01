-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_444cd434_7013_46bb_9e82_d756827f6b0e_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:47:44.510472+00:00
-- url     : https://prove2.me/submissions/a166ba86-2d1d-4358-8cfa-889f180816fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_lower_bound__p2m_77d34f95_c28b_41e7_bbec_f475d739e777_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      K.edgeFinset ⊆ L.edgeFinset ->
      WilliamsonShmoys.HasPlanarDrawingOn L ->
      L.edgeFinset = K.edgeFinset) :
    3 * Fintype.card V - 6 <= K.edgeFinset.card := by
  obtain ⟨L, dL, hKL, hL, hbound⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_edge_lower_bound__p2m_77d34f95_c28b_41e7_bbec_f475d739e777_a2
      K dK hK hcard
  have heq : L.edgeFinset = K.edgeFinset := hmax L dL hKL hL
  rw [← heq]
  exact hbound