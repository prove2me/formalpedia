-- Prove2me | solution 1 for WilliamsonShmoys.drawable_disconnected_edge_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:19:21.232403+00:00
-- url     : https://prove2.me/submissions/33e8e016-7c3e-49a0-9c9a-390e0e78d695
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_has_nonadjacent_pair
import Theorems.Thm_WilliamsonShmoys_drawing_adds_nonadjacent_edge

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 ≤ Fintype.card V)
    (hdisc : ¬ Q.Connected) :
    ∃ M : SimpleGraph V,
      Q ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∃ u v, M.Adj u v ∧ ¬ Q.Adj u v := by
  obtain ⟨u, v, huv, hnot⟩ :=
    WilliamsonShmoys.disconnected_has_nonadjacent_pair Q hV hdisc
  obtain ⟨M, hQM, hM, hnew⟩ :=
    WilliamsonShmoys.drawing_adds_nonadjacent_edge Q hQ u v huv hnot
  exact ⟨M, hQM, hM, u, v, hnew⟩