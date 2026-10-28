-- Prove2me | solution 1 for WilliamsonShmoys.connected_of_maximal_drawable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:53:05.335888+00:00
-- url     : https://prove2.me/submissions/61e1eb43-02d8-433b-9ecb-b230c04ef21c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_strict_supergraph_of_disconnected_drawing

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ J : SimpleGraph V,
      K ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ K) :
    K.Connected := by
  by_contra hNotConnected
  obtain ⟨J, hKJ, hNotJK, hJDraw⟩ :=
    WilliamsonShmoys.exists_drawable_strict_supergraph_of_disconnected_drawing
      K hV hDraw hNotConnected
  exact hNotJK (hMax J hKJ hJDraw)