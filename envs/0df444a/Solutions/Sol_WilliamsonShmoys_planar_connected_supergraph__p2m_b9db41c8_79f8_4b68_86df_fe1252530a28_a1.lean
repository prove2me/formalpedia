-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_supergraph__p2m_b9db41c8_79f8_4b68_86df_fe1252530a28_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:45:36.411941+00:00
-- url     : https://prove2.me/submissions/a2e577fa-a91a-44c1-8cbb-fea71b237aa7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_planar_bridge_extension_implies_connected_extension__p2m_f9b838b0_f6aa_487e_9e1a_71f80b7ae2c4_a1
import Theorems.Thm_WilliamsonShmoys_planar_join_separated_vertices__p2m_f9b838b0_f6aa_487e_9e1a_71f80b7ae2c4_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K := by
  apply WilliamsonShmoys.finite_planar_bridge_extension_implies_connected_extension__p2m_f9b838b0_f6aa_487e_9e1a_71f80b7ae2c4_a1
    H hH
  intro G hHG hG u v hnot
  obtain ⟨K, hGK, hReach, hK⟩ :=
    WilliamsonShmoys.planar_join_separated_vertices__p2m_f9b838b0_f6aa_487e_9e1a_71f80b7ae2c4_a1
      G hG hnot
  exact ⟨K, hGK, hK, hReach⟩