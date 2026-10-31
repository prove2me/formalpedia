-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_maximal_extension__p2m_c603be23_9a74_4dd9_9858_66dd86a4b903_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:52:57.052657+00:00
-- url     : https://prove2.me/submissions/6d8f59fb-9694-4b46-a383-508b312d9191

import Theorems.Thm_WilliamsonShmoys_drawable_edge_maximal_extension__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L :=
  WilliamsonShmoys.drawable_edge_maximal_extension__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1 K hK
