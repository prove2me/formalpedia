-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_maximal_2d69255633d74159
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:01:35.360754+00:00
-- url     : https://prove2.me/submissions/e76a2bf7-72b2-49b2-9d67-55b3404243c5

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
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ P : SimpleGraph V, G.edgeSet ⊆ P.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V, P.edgeSet ⊆ Q.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn Q → Q.edgeSet ⊆ P.edgeSet := by
  obtain ⟨R, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn G hG
  refine ⟨R, SimpleGraph.edgeSet_subset_edgeSet.2 h1, h2, fun S hRS hS => ?_⟩
  rw [h3 S (SimpleGraph.edgeSet_subset_edgeSet.1 hRS) hS]
