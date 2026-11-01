-- Prove2me | solution 1 for WilliamsonShmoys.planar_add_bridge_across_cut__p2m_bb71a8e8_4f54_44cc_a603_6794a7a0cd2a_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:22:03.619548+00:00
-- url     : https://prove2.me/submissions/964568c7-c898-48e9-8d1f-8cb751ba00ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_add_bridge_between_disconnected_vertices__p2m_05c1a0b4_69ca_4d36_9f49_0774601d7f45_a1
import Theorems.Thm_WilliamsonShmoys_cut_implies_not_reachable__p2m_05c1a0b4_69ca_4d36_9f49_0774601d7f45_a3
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    {u v : V} (A : Set V) (huA : u ∈ A) (hvA : v ∉ A)
    (hcut : ∀ {x y : V}, x ∈ A → y ∉ A → ¬ G.Adj x y) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ HasPlanarDrawingOn K ∧ K.Adj u v := by
  apply WilliamsonShmoys.planar_add_bridge_between_disconnected_vertices__p2m_05c1a0b4_69ca_4d36_9f49_0774601d7f45_a1 G hG
  exact WilliamsonShmoys.cut_implies_not_reachable__p2m_05c1a0b4_69ca_4d36_9f49_0774601d7f45_a3 G A huA hvA hcut