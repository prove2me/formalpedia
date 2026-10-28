-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_planar_extension_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:45:56.801141+00:00
-- url     : https://prove2.me/submissions/607fc2aa-aa38-4145-89dd-9217db19f2f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension_for_edge_count
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_for_extension

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨J, hHJ, hJ, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_extension_for_edge_count H hH
  exact ⟨J, hHJ, hJ,
    WilliamsonShmoys.edge_maximal_planar_edge_count_for_extension J hJ hV hmax⟩