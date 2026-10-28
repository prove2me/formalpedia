-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_tight_edge_count_20261028_job9e56ac28
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:53:44.018833+00:00
-- url     : https://prove2.me/submissions/d1b3ad5a-ba46-473f-9b4d-cd2c2be455f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_job9e56ac28_v2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_ncard_triangulation_job9e56ac28_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hLplanar, hLmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_job9e56ac28_v2 K hKplanar
  have hcount :=
    WilliamsonShmoys.maximal_planar_ncard_triangulation_job9e56ac28_v2 L hV hLplanar hLmax
  exact ⟨L, hKL, hLplanar, hcount⟩