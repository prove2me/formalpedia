-- Prove2me | solution 2 for WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_count_v2_0463fea4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T13:02:59.262706+00:00
-- url     : https://prove2.me/submissions/0b74c21a-9b32-45a4-9200-cfce7c1d3bf7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem S181max {V : Type} [Fintype V] (Q : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : Q G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ Q H ∧ ∀ K : SimpleGraph V, H ≤ K → Q K → K = H := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ Q J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨G, le_rfl, hG⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun N hN hPN =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN) hN⟩

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      Set.Subset Q.edgeSet R.edgeSet ∧
      ∀ S : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn S →
        Set.Subset R.edgeSet S.edgeSet →
        S.edgeSet = R.edgeSet := by
  obtain ⟨R, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn Q hQ
  refine ⟨R, h2, SimpleGraph.edgeSet_subset_edgeSet.2 h1, fun S hS hRS => ?_⟩
  rw [h3 S (SimpleGraph.edgeSet_subset_edgeSet.1 hRS) hS]
