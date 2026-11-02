-- Prove2me | solution 2 for WilliamsonShmoys_planar_connected_extension__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:11:59.409268+00:00
-- url     : https://prove2.me/submissions/cbd38bd3-c4ad-4979-9d7e-c550354b9b03

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V), HasPlanarDrawingOn H →
    ∃ G : SimpleGraph V, H ≤ G ∧ HasPlanarDrawingOn G ∧ G.Connected) := by
  intro h
  let H : SimpleGraph Empty := ⊤
  have hDraw : HasPlanarDrawingOn H := by
    unfold HasPlanarDrawingOn
    refine ⟨(fun x : Empty => x.elim), (fun x : Empty => x.elim), ?_⟩
    constructor
    · intro x y hxy
      cases x
    · constructor
      · intro u
        cases u
      · intro u
        cases u
  obtain ⟨G, hHG, hGDraw, hGConnected⟩ := h H hDraw
  rcases hGConnected.nonempty with ⟨v⟩
  exact nomatch v