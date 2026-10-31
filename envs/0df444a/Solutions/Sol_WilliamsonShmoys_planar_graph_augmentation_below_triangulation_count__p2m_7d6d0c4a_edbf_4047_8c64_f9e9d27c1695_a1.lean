-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_augmentation_below_triangulation_count__p2m_7d6d0c4a_edbf_4047_8c64_f9e9d27c1695_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:38:31.727415+00:00
-- url     : https://prove2.me/submissions/c0c95a4d-5ebd-4b78-8f86-744e34654029

import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_below_max_20261026

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 <= Fintype.card V) (hSmall : G.edgeSet.ncard < 3 * Fintype.card V - 6) : ∃ K : SimpleGraph V, G ≤ K ∧ K ≠ G ∧ WilliamsonShmoys.HasPlanarDrawingOn K :=
  WilliamsonShmoys.planar_edge_augmentation_below_max_20261026 G hDraw hV hSmall
