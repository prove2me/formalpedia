-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_7cf72e3d_7b9d_4e33_bfe4_614d5c224b98_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:24:16.345153+00:00
-- url     : https://prove2.me/submissions/29b82d22-70bc-436d-869d-4ae4fb775d97

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (dM : DecidableRel M.Adj) (hM : HasPlanarDrawingOn M) (hcard : 3 <= Fintype.card V) (hmax : ∀ (N : SimpleGraph V) (dN : DecidableRel N.Adj), M <= N → HasPlanarDrawingOn N → N = M) : 3 * Fintype.card V <= M.edgeFinset.card + 6 := by
  classical
  have hMax' : ∀ J : SimpleGraph V, M ≤ J → HasPlanarDrawingOn J → J ≤ M := by
    intro J hMJ hJ
    exact le_of_eq (hmax J (Classical.decRel _) hMJ hJ)
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc M hcard hM hMax'
  have h1 : M.edgeSet.ncard = M.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  omega
