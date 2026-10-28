-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_component_step
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:32:56.045292+00:00
-- url     : https://prove2.me/submissions/85335c89-8ec6-4e83-96d7-9afba3f504a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_unreachable_pair_of_card_ge_three
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_add_edge

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hV : 3 <= Fintype.card V)
    (hnotConnected : ¬ P.Connected) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      (∀ u v, P.Reachable u v → Q.Reachable u v) ∧
      ∃ u v, ¬ P.Reachable u v ∧ Q.Reachable u v := by
  obtain ⟨u, v, huv, hnotReachable⟩ :=
    WilliamsonShmoys.exists_unreachable_pair_of_card_ge_three P hV hnotConnected
  obtain ⟨Q, hPQ, hQdraw, hpreserves, hQreachable⟩ :=
    WilliamsonShmoys.planar_drawingOn_add_edge P hdraw u v huv hnotReachable
  exact ⟨Q, hPQ, hQdraw, hpreserves, ⟨u, v, hnotReachable, hQreachable⟩⟩