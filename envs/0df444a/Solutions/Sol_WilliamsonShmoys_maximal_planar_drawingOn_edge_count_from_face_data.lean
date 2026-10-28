-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_edge_count_from_face_data
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:10:58.404844+00:00
-- url     : https://prove2.me/submissions/0afaf596-88ba-427f-a3ff-2917fecf85e9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edgeSet_ncard_le
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edgeSet_ncard_ge

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J) :
    J.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := WilliamsonShmoys.planar_drawingOn_edgeSet_ncard_le J hDraw hCard
  have hLower := WilliamsonShmoys.maximal_planar_drawingOn_edgeSet_ncard_ge J hDraw hCard hMax
  omega