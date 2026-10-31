-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_21bb1f42_93f8_4aca_8bd1_86213d966802_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:45:26.308625+00:00
-- url     : https://prove2.me/submissions/85771cca-9c2a-455a-bee2-b77e83bc0a9b

import Theorems.Thm_WilliamsonShmoys_drawable_edge_maximal_extension__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L :=
  WilliamsonShmoys.drawable_edge_maximal_extension__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1 K hK
