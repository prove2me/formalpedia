-- Prove2me | solution 1 for WilliamsonShmoys_inclusion_maximal_planar_graph_has_euler_edge_count__p2m_b372cfef_764e_41b9_a3f0_cf4f0282f71c_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:28:35.885016+00:00
-- url     : https://prove2.me/submissions/b915d746-4d89-4e92-98d5-6b39e9004081
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_euler_edge_count__p2m_47c18254_8e9b_4a76_b436_1915ac92f140_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn H →
      L.edgeFinset ⊆ H.edgeFinset → H.edgeFinset = L.edgeFinset) :
    L.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨H, dH, hH, hsub, hcount⟩ :=
    WilliamsonShmoys_planar_supergraph_with_euler_edge_count__p2m_47c18254_8e9b_4a76_b436_1915ac92f140_a1
      L dL hL hcard
  have heq := hmax H dH hH hsub
  rw [← heq]
  exact hcount