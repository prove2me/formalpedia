-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_edge_count_df5b7716_886f_4c81_a3fd_ebfa1ccd5c5b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:38:19.513983+00:00
-- url     : https://prove2.me/submissions/5accb059-1c9f-43a3-9a28-643b1bde1aa2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_has_triangulated_extension
set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_drawingOn_has_triangulated_extension H hH hV
  have hEq : K = H := hmax K hHK hK
  simpa [hEq] using hcount