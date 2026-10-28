-- Prove2me | solution 2 for WilliamsonShmoys.planar_completion_exists_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:32:31.493985+00:00
-- url     : https://prove2.me/submissions/26bea4fc-32e1-4a4b-80fa-e248a80df4be

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
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      M.edgeSet ⊆ L.edgeSet ∧
      (∀ K : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn K →
        L.edgeSet ⊆ K.edgeSet → K.edgeSet = L.edgeSet) := by
  obtain ⟨L, h1, h2, h3⟩ := S181max _ M hM
  refine ⟨L, h2, SimpleGraph.edgeSet_subset_edgeSet.2 h1, fun K hK hs => ?_⟩
  rw [h3 K (SimpleGraph.edgeSet_subset_edgeSet.1 hs) hK]
