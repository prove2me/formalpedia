-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_repair_8fa97b2b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:52:43.558148+00:00
-- url     : https://prove2.me/submissions/81d59e60-743e-43f9-9b1e-0b439fc38486

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
    ∃ H : SimpleGraph V,
      M.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet ⊆ H.edgeSet := by
  obtain ⟨K, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn M hM
  exact ⟨K, SimpleGraph.edgeSet_mono h1, h2, fun L hL hd => by
    rw [h3 L (SimpleGraph.edgeSet_subset_edgeSet.1 hL) hd]⟩
