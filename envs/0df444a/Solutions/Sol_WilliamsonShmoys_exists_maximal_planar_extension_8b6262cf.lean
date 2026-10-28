-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension_8b6262cf
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:32:32.252855+00:00
-- url     : https://prove2.me/submissions/1155b37e-0f42-44b0-bafe-24fb06301cda

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
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ H : SimpleGraph V,
        L.edgeSet ⊆ H.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn H →
        L.edgeSet = H.edgeSet := by
  obtain ⟨L, h1, h2, h3⟩ := S181max _ K hK
  refine ⟨L, SimpleGraph.edgeSet_subset_edgeSet.2 h1, h2, fun H hs hH => ?_⟩
  rw [h3 H (SimpleGraph.edgeSet_subset_edgeSet.1 hs) hH]
