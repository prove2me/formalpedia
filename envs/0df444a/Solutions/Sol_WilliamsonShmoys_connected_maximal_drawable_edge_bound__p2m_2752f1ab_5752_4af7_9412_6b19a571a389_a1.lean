-- Prove2me | solution 1 for WilliamsonShmoys.connected_maximal_drawable_edge_bound__p2m_2752f1ab_5752_4af7_9412_6b19a571a389_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:24:17.018651+00:00
-- url     : https://prove2.me/submissions/32fb3713-0d16-45d3-9cee-eeb6318d9c3a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (dM : DecidableRel M.Adj) (hM : HasPlanarDrawingOn M) (hcard : 3 <= Fintype.card V) (hmax : forall (N : SimpleGraph V) (dN : DecidableRel N.Adj), M <= N -> HasPlanarDrawingOn N -> N = M) (hconn : M.Connected) : 3 * Fintype.card V <= M.edgeFinset.card + 6 := by
  classical
  have hMax' : ∀ J : SimpleGraph V, M ≤ J → HasPlanarDrawingOn J → J ≤ M := by
    intro J hMJ hJ
    exact le_of_eq (hmax J (Classical.decRel _) hMJ hJ)
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc M hcard hM hMax'
  have h1 : M.edgeSet.ncard = M.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  omega
