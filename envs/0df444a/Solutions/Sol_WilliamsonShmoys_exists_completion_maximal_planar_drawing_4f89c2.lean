-- Prove2me | solution 1 for WilliamsonShmoys.exists_completion_maximal_planar_drawing_4f89c2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T13:03:00.021868+00:00
-- url     : https://prove2.me/submissions/76095e67-2401-41ff-a28b-b4c801c2b6e3

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
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 <= Fintype.card V) :
    ∃ R : SimpleGraph V,
      Q.edgeSet ⊆ R.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      ∀ S : SimpleGraph V, R.edgeSet ⊂ S.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn S := by
  obtain ⟨R, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn Q hQ
  refine ⟨R, SimpleGraph.edgeSet_subset_edgeSet.2 h1, h2, fun S hRS hS => ?_⟩
  have := h3 S (SimpleGraph.edgeSet_subset_edgeSet.1 hRS.1) hS
  subst this
  exact hRS.2 le_rfl
