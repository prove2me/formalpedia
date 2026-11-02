-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_afc05135_ebe6_4750_8043_cdffdef73084_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:53:22.934063+00:00
-- url     : https://prove2.me/submissions/ed09309e-9f8f-4c6c-8e3f-4b7ce40e9544
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulation_supergraph__p2m_a2db6ec5_2f79_4623_a999_eb974cadd653_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L → H ≤ L → L = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     3 * Fintype.card V ≤ H.edgeFinset.card + 6) := by
  classical
  obtain ⟨L, hLdraw, hHL, hLcard⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulation_supergraph__p2m_a2db6ec5_2f79_4623_a999_eb974cadd653_a1
      H hcard hdraw
  have hLH : L = H := hmax L hLdraw hHL
  rw [hLH] at hLcard
  omega
