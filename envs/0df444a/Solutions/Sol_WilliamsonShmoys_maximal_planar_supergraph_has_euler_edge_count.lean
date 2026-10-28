-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_has_euler_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:04:58.33856+00:00
-- url     : https://prove2.me/submissions/85987332-b993-4fe7-ad36-a09c1e67bdab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_euler_edge_count_completion
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V,
      H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨J, hHJ, hPlanar, hCount⟩ :=
    WilliamsonShmoys.exists_planar_euler_edge_count_completion H hV hH
  have hEq : J = H := hMax J hHJ hPlanar
  rw [← hEq]
  exact hCount