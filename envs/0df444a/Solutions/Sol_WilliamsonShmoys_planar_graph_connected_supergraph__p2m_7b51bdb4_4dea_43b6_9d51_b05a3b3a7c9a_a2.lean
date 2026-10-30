-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_connected_supergraph__p2m_7b51bdb4_4dea_43b6_9d51_b05a3b3a7c9a_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:44:37.519165+00:00
-- url     : https://prove2.me/submissions/07f2c57b-0521-4b33-9df2-4df450bfd84c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_add_bridge__p2m_e87f3d6d_f5ac_4caa_95af_19e806d71ee4_a2
import Theorems.Thm_WilliamsonShmoys_planar_graph_connected_completion_from_bridge_property__p2m_e87f3d6d_f5ac_4caa_95af_19e806d71ee4_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hne : Nonempty V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ (∀ x y, N.Reachable x y) ∧ HasPlanarDrawingOn N := by
  exact WilliamsonShmoys.planar_graph_connected_completion_from_bridge_property__p2m_e87f3d6d_f5ac_4caa_95af_19e806d71ee4_a2
    M HasPlanarDrawingOn hM hne
    (by
      intro G hG x y hxy
      exact WilliamsonShmoys.planar_graph_add_bridge__p2m_e87f3d6d_f5ac_4caa_95af_19e806d71ee4_a2
        G hG x y hxy)
