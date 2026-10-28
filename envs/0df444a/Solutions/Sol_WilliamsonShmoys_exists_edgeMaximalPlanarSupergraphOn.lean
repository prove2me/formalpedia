-- Prove2me | solution 1 for WilliamsonShmoys.exists_edgeMaximalPlanarSupergraphOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T13:31:48.253791+00:00
-- url     : https://prove2.me/submissions/1b54b67f-a9fe-4a29-b66c-bab46c72c986

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
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V, N.edgeSet ⊂ P.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn P := by
  obtain ⟨R, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn M hM
  refine ⟨R, SimpleGraph.edgeSet_subset_edgeSet.2 h1, h2, fun S hRS hS => ?_⟩
  have := h3 S (SimpleGraph.edgeSet_subset_edgeSet.1 hRS.1) hS
  subst this
  exact hRS.2 le_rfl
