-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_connected_planar_supergraph__p2m_8eefeb5d_6bb8_407d_b469_57becc19650a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:42:14.862928+00:00
-- url     : https://prove2.me/submissions/e5c12df0-4a1e-47a7-b1ec-c6ef0d23c438
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_one_edge_extension__p2m_2deb786e_0280_4a79_a944_d66b43964e65_a1
import Theorems.Thm_WilliamsonShmoys_supergraph_extension_closure__p2m_2deb786e_0280_4a79_a944_d66b43964e65_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) ∧
      H.Connected ∧ HasPlanarDrawingOn H := by
  apply WilliamsonShmoys.supergraph_extension_closure__p2m_2deb786e_0280_4a79_a944_d66b43964e65_a1
    (P := HasPlanarDrawingOn) G hG
  intro K hK hKnc
  obtain ⟨H, hsub, ⟨u, v, hnotReachable, hnewAdj⟩, hH⟩ :=
    WilliamsonShmoys.planar_drawing_one_edge_extension__p2m_2deb786e_0280_4a79_a944_d66b43964e65_a1
      K hK hKnc
  refine ⟨H, hsub, ⟨u, v, ?_, hnewAdj⟩, hH⟩
  intro hadj
  exact hnotReachable hadj.reachable