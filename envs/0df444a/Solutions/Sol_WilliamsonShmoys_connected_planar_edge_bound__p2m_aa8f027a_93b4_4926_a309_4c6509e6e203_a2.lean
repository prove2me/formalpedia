-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_aa8f027a_93b4_4926_a309_4c6509e6e203_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:27:47.904458+00:00
-- url     : https://prove2.me/submissions/4131a2db-473f-49a0-af23-de0f5035edb4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_faceCounts__p2m_9ccf8ab9_0495_4b50_8b51_030e6fe4c678_a2
import Theorems.Thm_WilliamsonShmoys_faceCounts_edgeBound__p2m_9ccf8ab9_0495_4b50_8b51_030e6fe4c678_a2
set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hConnected : H.Connected) (hDraw : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) : H.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨F, faceLength, hEuler, hIncidences, hFaceLength⟩ :=
    WilliamsonShmoys.planarDrawingOn_faceCounts__p2m_9ccf8ab9_0495_4b50_8b51_030e6fe4c678_a2
      H hConnected hDraw hV
  exact WilliamsonShmoys.faceCounts_edgeBound__p2m_9ccf8ab9_0495_4b50_8b51_030e6fe4c678_a2
    H F faceLength hEuler hIncidences hFaceLength hV