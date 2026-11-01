-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_cut_bridge__p2m_016bc9c9_be0e_41b2_afe4_acfa54df6433_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:39:22.328617+00:00
-- url     : https://prove2.me/submissions/4fd3544c-c742-40c4-8be0-c8d0705801b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_cut_separates_reachability__p2m_eb8f4cd8_f0b2_4542_934a_57c382c5e901_a1
import Theorems.Thm_WilliamsonShmoys_planar_add_bridge_between_components__p2m_eb8f4cd8_f0b2_4542_934a_57c382c5e901_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    {u v : V} (s : Set V)
    (hu : u ∈ s) (hv : v ∉ s)
    (hcut : ∀ x y, G.Adj x y → (x ∈ s ↔ y ∈ s)) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ HasPlanarDrawingOn K ∧ K.Adj u v := by
  have hdis : ¬ G.Reachable u v :=
    WilliamsonShmoys.cut_separates_reachability__p2m_eb8f4cd8_f0b2_4542_934a_57c382c5e901_a1
      G s hu hv hcut
  exact WilliamsonShmoys.planar_add_bridge_between_components__p2m_eb8f4cd8_f0b2_4542_934a_57c382c5e901_a1
    G hG hdis