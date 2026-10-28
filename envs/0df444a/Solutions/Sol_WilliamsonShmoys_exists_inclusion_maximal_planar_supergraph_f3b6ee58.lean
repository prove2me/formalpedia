-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph_f3b6ee58
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:40:41.160139+00:00
-- url     : https://prove2.me/submissions/01f13957-f32d-4163-b467-b28c84df98b4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem S181max {V : Type} [Fintype V] (Q : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : Q G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ Q H ∧ ∀ K : SimpleGraph V, H ≤ K → Q K → K = H := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ Q J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨G, le_rfl, hG⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun N hN hPN =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN) hN⟩

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      L.edgeSet ⊆ K.edgeSet ∧
      ∀ K' : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn K' →
        K.edgeSet ⊆ K'.edgeSet →
        K'.edgeSet ⊆ K.edgeSet := by
  obtain ⟨K, h1, h2, h3⟩ := S181max _ L hL
  refine ⟨K, h2, SimpleGraph.edgeSet_subset_edgeSet.2 h1, fun K' hK hs => ?_⟩
  rw [h3 K' (SimpleGraph.edgeSet_subset_edgeSet.1 hs) hK]
