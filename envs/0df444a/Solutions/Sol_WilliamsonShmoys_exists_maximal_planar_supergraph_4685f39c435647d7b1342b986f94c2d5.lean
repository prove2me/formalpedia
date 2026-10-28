-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_4685f39c435647d7b1342b986f94c2d5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:58:10.073903+00:00
-- url     : https://prove2.me/submissions/9dad22d6-b9eb-49f5-91d8-fa4e24e7fd58

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
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ K' : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K' ∧
      K.edgeSet ⊆ K'.edgeSet ∧
      ∀ H : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn H →
        K'.edgeSet ⊆ H.edgeSet →
        H.edgeSet ⊆ K'.edgeSet := by
  obtain ⟨L, h1, h2, h3⟩ := S181max _ K hK
  refine ⟨L, h2, SimpleGraph.edgeSet_subset_edgeSet.2 h1, fun H hH hs => ?_⟩
  rw [h3 H (SimpleGraph.edgeSet_subset_edgeSet.1 hs) hH]
