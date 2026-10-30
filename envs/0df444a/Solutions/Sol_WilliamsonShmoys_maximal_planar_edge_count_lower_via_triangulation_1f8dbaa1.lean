-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_via_triangulation_1f8dbaa1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:04:20.211982+00:00
-- url     : https://prove2.me/submissions/fc612716-2f1f-4ed6-80c4-86ad854ce7dc

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_exact_edge_count
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall J : SimpleGraph V,
      H <= J -> WilliamsonShmoys.HasPlanarDrawingOn J -> J = H) :
    3 * Fintype.card V <= H.edgeSet.ncard + 6 := by
  obtain ⟨J, hHJ, hJdraw, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_exact_edge_count H hV hH
  have hEq : J = H := hmax J hHJ hJdraw
  rw [hEq] at hcount
  omega