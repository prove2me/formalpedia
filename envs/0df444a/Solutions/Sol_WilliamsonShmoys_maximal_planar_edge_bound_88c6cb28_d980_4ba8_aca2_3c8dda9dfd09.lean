-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound_88c6cb28_d980_4ba8_aca2_3c8dda9dfd09
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:57:57.873219+00:00
-- url     : https://prove2.me/submissions/95daed5c-0a35-4d02-a832-d32ac38b3f01

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_completion
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMaximal : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKPlanar, hKEdges⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation_completion H hV hH
  have hKH : K ≤ H := hMaximal K hHK hKPlanar
  have hEq : K = H := le_antisymm hKH hHK
  simpa [hEq] using hKEdges.le
