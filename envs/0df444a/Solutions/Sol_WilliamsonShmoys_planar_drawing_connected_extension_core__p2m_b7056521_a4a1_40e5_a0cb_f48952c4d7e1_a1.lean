-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_core__p2m_b7056521_a4a1_40e5_a0cb_f48952c4d7e1_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:40:06.720443+00:00
-- url     : https://prove2.me/submissions/feb5a5b6-710f-4d3b-9c8f-ea725de681ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_bridge_forest_extension__p2m_16420d1a_8336_4ecd_8bbd_58603af5ab15_a1
import Theorems.Thm_WilliamsonShmoys_exists_component_bridge_forest__p2m_16420d1a_8336_4ecd_8bbd_58603af5ab15_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K := by
  classical
  obtain ⟨ F, hStar, hAcross, hConnected ⟩ :=
    WilliamsonShmoys.exists_component_bridge_forest__p2m_16420d1a_8336_4ecd_8bbd_58603af5ab15_a1 H
  refine ⟨ H ⊔ F, le_sup_left, hConnected, ?_ ⟩
  exact WilliamsonShmoys.planar_bridge_forest_extension__p2m_16420d1a_8336_4ecd_8bbd_58603af5ab15_a1 H F hH hStar hAcross hConnected