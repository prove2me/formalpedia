-- Prove2me | solution 1 for WilliamsonShmoys.maximal_fixed_vertex_planar_edge_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:59:31.893508+00:00
-- url     : https://prove2.me/submissions/237603e3-20cf-4ba6-a245-1827ea51b0ea

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_extension_fixed_vertex_type_5c9b79f9_9987_414e_a99c_5e863a94cdb9

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall H : SimpleGraph V,
      K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K) :
    3 * Fintype.card V - 6 <= K.edgeSet.ncard := by
  obtain ⟨H, hKH, hH, hEdges⟩ :=
    WilliamsonShmoys.planar_edge_bound_extension_fixed_vertex_type_5c9b79f9_9987_414e_a99c_5e863a94cdb9
      K hV hK
  have hHK : H <= K := hmax H hKH hH
  have hEq : K = H := le_antisymm hKH hHK
  simpa [hEq] using hEdges