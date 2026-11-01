-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_triangulated_supergraph__p2m_694a8160_ff76_4855_a03b_16e16dbb37d5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:35:30.327825+00:00
-- url     : https://prove2.me/submissions/736f1969-aee9-4f23-8cc4-39c4e91fd782
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_planar_supergraph__p2m_bc038eff_dd8d_4b01_9048_8ba39788938c_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_bc038eff_dd8d_4b01_9048_8ba39788938c_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    exists L : SimpleGraph V,
      (forall {u v : V}, K.Adj u v -> L.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn L /\
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj
       L.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.drawable_graph_has_maximal_planar_supergraph__p2m_bc038eff_dd8d_4b01_9048_8ba39788938c_a1
      K hK hcard
  refine ⟨L, hKL, hL, ?_⟩
  apply WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_bc038eff_dd8d_4b01_9048_8ba39788938c_a1
    L hL hcard
  intro M hLM hM
  intro u v huv
  exact hmax M (by
    intro u v huvK
    exact hLM (hKL huvK)) hM huv
