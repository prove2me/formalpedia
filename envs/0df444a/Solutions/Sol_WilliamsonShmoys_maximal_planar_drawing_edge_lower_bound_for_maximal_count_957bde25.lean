-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_for_maximal_count_957bde25
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:19:31.829153+00:00
-- url     : https://prove2.me/submissions/7aad9b6b-0edc-4836-8ddf-beb52d7611de

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_for_maximal_count_957bde25
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count_for_maximal_count_957bde25

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) :
    3 * Fintype.card V - 6 <= L.edgeSet.ncard := by
  obtain ⟨K, hLK, hK, hKmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension_for_maximal_count_957bde25 L hL
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_for_maximal_count_957bde25
      K hV hK hKmax
  have hKL : K = L := hmax K hLK hK
  rw [hKL] at hcount
  omega