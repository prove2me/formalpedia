-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_maximal_drawable__p2m_df288277_9c1c_43a5_8845_caf345f4f17a_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:42:16.842571+00:00
-- url     : https://prove2.me/submissions/0fd3cc17-f856-4273-bbdc-22d008014702

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : Set V) [Fintype S]
    (N : SimpleGraph S)
    (hDraw : HasPlanarDrawingOn N)
    (hcard : 3 ≤ S.ncard)
    (hmax : ∀ M : SimpleGraph S, N ≤ M → HasPlanarDrawingOn M → M = N) :
    3 * S.ncard ≤ N.edgeSet.ncard + 6 := by
  have hs : S.ncard = Fintype.card S := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  have hMax' : ∀ J : SimpleGraph _, N ≤ J → HasPlanarDrawingOn J → J ≤ N := by
    intro J hHJ hJ
    exact (hmax J hHJ hJ).le
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc N (by omega) hDraw hMax'
  omega
