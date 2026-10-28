-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_maximal_supergraph_repair_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:52:43.030344+00:00
-- url     : https://prove2.me/submissions/1c0e7b80-6cf2-454d-93b9-394f31f55236

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

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V) : ∃ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N ∧ M.edgeSet ⊆ N.edgeSet ∧ (∀ H : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn H → N.edgeSet ⊆ H.edgeSet → H.edgeSet ⊆ N.edgeSet) := by
  obtain ⟨N, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn M hM
  refine ⟨N, h2, SimpleGraph.edgeSet_subset_edgeSet.2 h1, fun H hH hs => ?_⟩
  rw [h3 H (SimpleGraph.edgeSet_subset_edgeSet.1 hs) hH]
