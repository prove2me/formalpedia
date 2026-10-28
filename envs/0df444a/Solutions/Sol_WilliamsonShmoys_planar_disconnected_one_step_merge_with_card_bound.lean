-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_one_step_merge_with_card_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:34:18.739923+00:00
-- url     : https://prove2.me/submissions/7176ace6-ed03-4a57-8f99-0335dac63ccf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_has_nonreachable_pair_for_merge
import Theorems.Thm_WilliamsonShmoys_planar_add_edge_across_components

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v := by
  obtain ⟨u, v, hNotReachable⟩ :=
    WilliamsonShmoys.disconnected_has_nonreachable_pair_for_merge G hV hDisconnected
  obtain ⟨H, hGH, hHPlanar, hAdj⟩ :=
    WilliamsonShmoys.planar_add_edge_across_components G hG hNotReachable
  exact ⟨H, hGH, hHPlanar, u, v, hNotReachable, hAdj⟩