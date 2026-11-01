-- Prove2me | solution 1 for WilliamsonShmoys.planar_add_bridge_between_components__p2m_eb8f4cd8_f0b2_4542_934a_57c382c5e901_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:55:46.933314+00:00
-- url     : https://prove2.me/submissions/960aae4d-af5a-4db6-8ca8-3d33534d48c5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_reachable_cut__p2m_bb71a8e8_4f54_44cc_a603_6794a7a0cd2a_a2
import Theorems.Thm_WilliamsonShmoys_planar_add_bridge_across_cut__p2m_bb71a8e8_4f54_44cc_a603_6794a7a0cd2a_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    {u v : V} (hdis : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ HasPlanarDrawingOn K ∧ K.Adj u v := by
  obtain ⟨A, huA, hvA, hcut⟩ :=
    WilliamsonShmoys.reachable_cut__p2m_bb71a8e8_4f54_44cc_a603_6794a7a0cd2a_a2
      G (u := u) (v := v) hdis
  exact WilliamsonShmoys.planar_add_bridge_across_cut__p2m_bb71a8e8_4f54_44cc_a603_6794a7a0cd2a_a2
    G hG (u := u) (v := v) A huA hvA hcut