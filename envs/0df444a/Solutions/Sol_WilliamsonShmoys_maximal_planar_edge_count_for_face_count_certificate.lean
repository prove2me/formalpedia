-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_face_count_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:16:52.954611+00:00
-- url     : https://prove2.me/submissions/cfd5646c-5837-416b-9885-bdc48a2be309
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_completion_efc6e0da

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V,
      H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨J, hHJ, hJDraw, hJCount⟩ :=
    WilliamsonShmoys.planar_edge_count_completion_efc6e0da H hV hH
  have hJH : J ≤ H := hMax J hHJ hJDraw
  have hEq : J = H := le_antisymm hJH hHJ
  rw [← hEq]
  exact hJCount
