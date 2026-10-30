-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:10:44.488868+00:00
-- url     : https://prove2.me/submissions/c0f4659f-40f2-4456-8067-3e4da0084487

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_8bed89f5_b4a1_4e0c_8939_cbf59f18f35d
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_8bed89f5_b4a1_4e0c_8939_cbf59f18f35d

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ R : SimpleGraph V,
      M ≤ R →
      WilliamsonShmoys.HasPlanarDrawingOn R →
      R ≤ M) :
    3 * Fintype.card V - 6 = M.edgeSet.ncard := by
  have hupper :=
    WilliamsonShmoys.planar_edge_count_upper_bound_8bed89f5_b4a1_4e0c_8939_cbf59f18f35d M hM hV
  have hlower :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound_8bed89f5_b4a1_4e0c_8939_cbf59f18f35d M hM hV hmax
  omega