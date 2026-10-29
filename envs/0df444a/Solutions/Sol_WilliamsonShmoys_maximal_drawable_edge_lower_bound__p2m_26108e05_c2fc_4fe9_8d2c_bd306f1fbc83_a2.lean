-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_26108e05_c2fc_4fe9_8d2c_bd306f1fbc83_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:01:08.444222+00:00
-- url     : https://prove2.me/submissions/4adf190d-6617-4f4e-93b4-01f28de875ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_edge_bound__p2m_b7437c67_f19b_46b7_abfb_8f1126c280d3_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet.ncard ≤ K.edgeSet.ncard) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hLDraw, hLower⟩ :=
    WilliamsonShmoys.drawable_supergraph_edge_bound__p2m_b7437c67_f19b_46b7_abfb_8f1126c280d3_a1
      K hDraw hCard
  have hUpper := hMax L hKL hLDraw
  omega