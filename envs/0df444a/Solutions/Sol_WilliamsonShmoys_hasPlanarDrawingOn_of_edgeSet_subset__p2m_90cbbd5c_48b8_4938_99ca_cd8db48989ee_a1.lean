-- Prove2me | solution 1 for WilliamsonShmoys.hasPlanarDrawingOn_of_edgeSet_subset__p2m_90cbbd5c_48b8_4938_99ca_cd8db48989ee_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:33:23.688442+00:00
-- url     : https://prove2.me/submissions/5cd689d4-db46-4115-8141-eb995669c4f3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_monotone_under_edge_subset__p2m_d8aa7015_594b_44f0_b66b_a7cd4c31cad4_a1

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : Set.Subset G.edgeSet H.edgeSet)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  first
  | exact _root_.WilliamsonShmoys.planar_drawing_monotone_under_edge_subset__p2m_d8aa7015_594b_44f0_b66b_a7cd4c31cad4_a1
  | (apply _root_.WilliamsonShmoys.planar_drawing_monotone_under_edge_subset__p2m_d8aa7015_594b_44f0_b66b_a7cd4c31cad4_a1 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_drawing_monotone_under_edge_subset__p2m_d8aa7015_594b_44f0_b66b_a7cd4c31cad4_a1 <;> assumption)
