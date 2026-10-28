-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_maximal_has_three_n_minus_six
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:14:05.850152+00:00
-- url     : https://prove2.me/submissions/2ed04ae0-5e10-4f3e-bf1d-42ea877f913d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulated_supergraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H <= K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.maximal_planar_triangulated_supergraph H hV hH
  have hEq : K = H := hmax K hHK hK
  simpa [hEq] using hcount