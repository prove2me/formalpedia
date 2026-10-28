-- Prove2me | solution 1 for WilliamsonShmoys.planar_augment_between_unreachable_vertices
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:56:54.192173+00:00
-- url     : https://prove2.me/submissions/5c8a76e1-5218-4c1c-a12f-c34110129509
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_connected_augmentation

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    {u v : V} (hUnreachable : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ G ≠ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  obtain ⟨K, hGK, hneq, _hConnected, hKPlanar⟩ :=
    WilliamsonShmoys.planar_connected_augmentation G hG hUnreachable
  exact ⟨K, hGK, hneq, hKPlanar⟩