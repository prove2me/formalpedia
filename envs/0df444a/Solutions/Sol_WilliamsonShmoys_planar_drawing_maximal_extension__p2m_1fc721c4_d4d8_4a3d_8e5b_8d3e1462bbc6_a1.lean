-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_1fc721c4_d4d8_4a3d_8e5b_8d3e1462bbc6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:41:59.529855+00:00
-- url     : https://prove2.me/submissions/5d27a3aa-3beb-451c-81d5-814524de2772

import Theorems.Thm_WilliamsonShmoys_drawable_edge_maximal_extension__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hS : HasPlanarDrawingOn S) : ∃ T : SimpleGraph V, S ≤ T ∧ HasPlanarDrawingOn T ∧ ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U = T :=
  WilliamsonShmoys.drawable_edge_maximal_extension__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1 S hS
