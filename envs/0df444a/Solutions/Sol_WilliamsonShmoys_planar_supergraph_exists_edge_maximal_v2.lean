-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_exists_edge_maximal_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T08:16:31.609099+00:00
-- url     : https://prove2.me/submissions/7d351e06-a9c1-4917-b812-b3c6497a44fe

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem S181max {V : Type} [Fintype V] (Q : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : Q G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ Q H ∧ ∀ K : SimpleGraph V, H ≤ K → Q K → K = H := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ Q J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨G, le_rfl, hG⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun N hN hPN =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN) hN⟩

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      Set.Subset P.edgeSet Q.edgeSet ∧
      ∀ R : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn R →
        Set.Subset Q.edgeSet R.edgeSet →
        R.edgeSet = Q.edgeSet := by
  obtain ⟨Q, h1, h2, h3⟩ := S181max _ P hP
  refine ⟨Q, h2, SimpleGraph.edgeSet_subset_edgeSet.2 h1, fun R hR hs => ?_⟩
  rw [h3 R (SimpleGraph.edgeSet_subset_edgeSet.1 hs) hR]
