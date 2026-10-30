-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_bound_maximal_graph_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:08:17.108557+00:00
-- url     : https://prove2.me/submissions/7d93bd43-401e-4e6d-ab44-884f7bfddf9a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hCount⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension_edge_count H hV hH
  have hEq : K = H := hMax K hHK hK
  rw [← hEq]
  exact le_of_eq hCount