-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_edge_between_components__p2m_f3cc24e6_d1b8_4aae_a4a3_597bfb5e0269_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:08:49.07972+00:00
-- url     : https://prove2.me/submissions/f97de55c-7e74-40aa-8a42-5cc1682cbc95
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_extension__p2m_3cdd0a1e_a971_4b42_9cfa_47309d863fea_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    {u v : V} (hSeparate : ¬ Nonempty (G.Walk u v)) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ G.edgeSet ⊂ H.edgeSet := by
  obtain ⟨H, hGH, hPlanar, hStrict, hBridge⟩ :=
    WilliamsonShmoys.planar_drawing_bridge_extension__p2m_3cdd0a1e_a971_4b42_9cfa_47309d863fea_a1
      G hG hSeparate
  exact ⟨H, hGH, hPlanar, hStrict⟩