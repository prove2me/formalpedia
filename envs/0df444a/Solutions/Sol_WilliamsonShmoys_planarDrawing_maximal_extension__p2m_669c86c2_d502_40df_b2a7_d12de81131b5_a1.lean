-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_maximal_extension__p2m_669c86c2_d502_40df_b2a7_d12de81131b5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:51:03.32255+00:00
-- url     : https://prove2.me/submissions/c43b9f3c-c253-4cf6-ab74-2a879e93cae4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finiteGraph_maximal_extension__p2m_131fddda_53be_4336_ab67_f2e30cf87311_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, LE.le L M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, LE.le M N → HasPlanarDrawingOn N → N = M := by
  exact WilliamsonShmoys.finiteGraph_maximal_extension__p2m_131fddda_53be_4336_ab67_f2e30cf87311_a1
    L HasPlanarDrawingOn hL