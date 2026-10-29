-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_via_triangulation_a4779231
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:04:13.524948+00:00
-- url     : https://prove2.me/submissions/b68377d1-3eb3-422e-bdd9-69fc3948a4d6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : forall L : SimpleGraph V,
      K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    3 * Fintype.card V - 6 <= K.edgeSet.ncard := by
  obtain ⟨L, hKL, hL, hEdge⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_edge_count K hV hK
  have hLK : L <= K := hMax L hKL hL
  have hEq : K = L := le_antisymm hKL hLK
  rw [hEq]
  simpa [hEdge]