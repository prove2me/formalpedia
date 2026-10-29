-- Prove2me | solution 1 for WilliamsonShmoys.simpleGraph_edge_upper_bound_of_connected_planar_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T00:31:55.094778+00:00
-- url     : https://prove2.me/submissions/4a0b4d56-1536-4604-b6c2-a22a6ec2098c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_completion__p2m_953852c9_9877_4510_aaba_a6b57c23a189_a4

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hConnected : H.Connected)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hHK, _hKDrawing, hKCount⟩ :=
    WilliamsonShmoys.planar_drawing_euler_completion__p2m_953852c9_9877_4510_aaba_a6b57c23a189_a4
      H hH hCard
  have hEdgeSubset : H.edgeSet ⊆ K.edgeSet :=
    SimpleGraph.edgeSet_subset_edgeSet.mpr hHK
  have hEdges : H.edgeSet.ncard ≤ K.edgeSet.ncard := Set.ncard_mono hEdgeSubset
  omega