-- Prove2me | solution 1 for WilliamsonShmoys_planar_connected_extension__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:01:13.364503+00:00
-- url     : https://prove2.me/submissions/5054a1fa-fb1a-4077-9ad4-a9a07832b75f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_extension_iter__p2m_1d8ffaac_75df_4ce0_8b03_9887c94b1bf3_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_step__p2m_1d8ffaac_75df_4ce0_8b03_9887c94b1bf3_a1
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V, H ≤ G ∧ HasPlanarDrawingOn G ∧ G.Connected := by
  apply WilliamsonShmoys_planar_connected_extension_iter__p2m_1d8ffaac_75df_4ce0_8b03_9887c94b1bf3_a1 H hH
  intro K hHK hK hKdisconnected
  exact WilliamsonShmoys_planar_drawing_bridge_step__p2m_1d8ffaac_75df_4ce0_8b03_9887c94b1bf3_a1 K hK hKdisconnected