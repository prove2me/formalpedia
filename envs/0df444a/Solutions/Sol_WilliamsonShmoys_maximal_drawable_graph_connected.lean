-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_connected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:55:30.364096+00:00
-- url     : https://prove2.me/submissions/1b95d5dc-0700-4e8e-9ceb-c418de2f6b8e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_disconnected_edge_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      Q ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M ≤ Q) :
    Q.Connected := by
  by_contra hconn
  obtain ⟨M, hQM, hMdraw, u, v, hMuv, hnotQ⟩ :=
    WilliamsonShmoys.drawable_disconnected_edge_extension Q hQ hV hconn
  exact hnotQ (hmax M hQM hMdraw hMuv)