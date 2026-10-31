-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_extension__p2m_5fdd342d_dc75_47e0_8287_8202cedefb2b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:47:27.72911+00:00
-- url     : https://prove2.me/submissions/5995d051-f323-40dc-b1e6-a964171b949c

import Theorems.Thm_WilliamsonShmoys_drawable_edge_maximal_extension__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L :=
  WilliamsonShmoys.drawable_edge_maximal_extension__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1 K hK
