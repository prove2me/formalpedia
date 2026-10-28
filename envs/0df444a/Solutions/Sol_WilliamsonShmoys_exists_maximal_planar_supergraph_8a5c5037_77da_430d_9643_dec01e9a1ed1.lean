-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_8a5c5037_77da_430d_9643_dec01e9a1ed1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T08:11:57.883905+00:00
-- url     : https://prove2.me/submissions/d184eb1d-cfff-4c45-99ce-8ac9ff968edd

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
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet ⊆ K.edgeSet := by
  obtain ⟨K, h1, h2, h3⟩ := S181max _ H hH
  refine ⟨K, SimpleGraph.edgeSet_subset_edgeSet.2 h1, h2, fun L hs hL => ?_⟩
  rw [h3 L (SimpleGraph.edgeSet_subset_edgeSet.1 hs) hL]
