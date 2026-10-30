-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_connected__p2m_bd5a0062_468c_43aa_a2a2_0a304df33140_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:27:53.351427+00:00
-- url     : https://prove2.me/submissions/5907e90e-9db1-4f67-9f2b-c83ece423af1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_supergraph__p2m_728b0cab_3e49_4ae4_a8bb_3f99be3d53bf_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hmax : ∀ G : SimpleGraph V, H ≤ G →
      WilliamsonShmoys.HasPlanarDrawingOn G → G = H)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 0 < Fintype.card V) : H.Connected := by
  by_contra hDisconnected
  obtain ⟨G, hHG, hne, hGDraw⟩ :=
    WilliamsonShmoys.disconnected_planar_supergraph__p2m_728b0cab_3e49_4ae4_a8bb_3f99be3d53bf_a2
      H hDraw hV hDisconnected
  exact hne (hmax G hHG hGDraw)