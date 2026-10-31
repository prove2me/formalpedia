-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_supergraph_ge3_c00979a8
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:22:06.399486+00:00
-- url     : https://prove2.me/submissions/251d5c33-52c1-483c-842b-72ebde88385a

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_with_edge_mono
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard :=
  WilliamsonShmoys.planar_drawing_connected_extension_with_edge_mono K hV hK
