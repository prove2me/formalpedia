-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_has_bridge_extension__p2m_319c6fe2_72dc_4179_bbfd_8ad17647c43d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:33:29.251994+00:00
-- url     : https://prove2.me/submissions/c8fad96e-d582-4323-aa1e-c60e96071c7a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_separated_bridge_extension__p2m_cb139db2_73c1_451e_b6a9_3cccdec58a46_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H)
    (hdisc : ¬ H.Connected) :
    ∃ u v : V, ∃ G : SimpleGraph V,
      ¬ H.Adj u v ∧ H ≤ G ∧ HasPlanarDrawingOn G ∧ G.Adj u v := by
  obtain ⟨u, v, huv, G, hHG, hG, hGuv, _⟩ :=
    WilliamsonShmoys.planar_separated_bridge_extension__p2m_cb139db2_73c1_451e_b6a9_3cccdec58a46_a2
      H hV hH hdisc
  exact ⟨u, v, G, huv, hHG, hG, hGuv⟩