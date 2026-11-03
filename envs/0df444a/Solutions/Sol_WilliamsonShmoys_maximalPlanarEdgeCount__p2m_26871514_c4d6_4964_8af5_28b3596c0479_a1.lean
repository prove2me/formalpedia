-- Prove2me | solution 1 for WilliamsonShmoys.maximalPlanarEdgeCount__p2m_26871514_c4d6_4964_8af5_28b3596c0479_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:11:09.861974+00:00
-- url     : https://prove2.me/submissions/f62dc16c-993b-46b8-9cc2-9d8021a425ba

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_638a1f84_48cf_416d_8d32_57bed5d6bb46_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hN : HasPlanarDrawingOn N)
    (hn : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      HasPlanarDrawingOn K →
      (letI : DecidableRel N.Adj := dN
       letI : DecidableRel K.Adj := dK
       N.edgeFinset ⊆ K.edgeFinset) →
      N = K) :
    letI : DecidableRel N.Adj := dN
    N.edgeFinset.card = 3 * Fintype.card V - 6 := by
  classical
  letI : DecidableRel N.Adj := dN
  have hm : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N := by
    intro K hle hK
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    have hs : N.edgeFinset ⊆ K.edgeFinset :=
      SimpleGraph.edgeFinset_subset_edgeFinset.mpr hle
    exact (hmax K (Classical.decRel K.Adj) hK hs).symm
  have hc :=
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_638a1f84_48cf_416d_8d32_57bed5d6bb46_a2
      N hN hn hm
  have hcard : N.edgeSet.ncard = N.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  exact hcard.symm.trans hc.symm
