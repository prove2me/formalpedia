-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:21:05.710998+00:00
-- url     : https://prove2.me/submissions/6b86a262-c157-4930-9e71-19b2bd056bdf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_drawing_edge_maximal_extension_3e41a808
import Theorems.Thm_WilliamsonShmoys_edge_count_of_planar_drawing_edge_maximal_3e41a808

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    Exists fun H : SimpleGraph V =>
      T ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hTH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_planar_drawing_edge_maximal_extension_3e41a808 T hT
  exact ⟨H, hTH, hH,
    WilliamsonShmoys.edge_count_of_planar_drawing_edge_maximal_3e41a808 H hV hH hmax⟩