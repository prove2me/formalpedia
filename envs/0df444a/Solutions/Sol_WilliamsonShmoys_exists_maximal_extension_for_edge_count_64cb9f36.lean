-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_extension_for_edge_count_64cb9f36
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:40:39.719123+00:00
-- url     : https://prove2.me/submissions/65ec958e-2145-4e71-ac09-0c291a2b2f34

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
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      N.edgeSet ⊆ P.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V,
        P.edgeSet ⊂ Q.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn Q := by
  obtain ⟨N0, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn N hN
  refine ⟨N0, SimpleGraph.edgeSet_subset_edgeSet.2 h1, h2, fun Q hN hNp => ?_⟩
  have hle : N0 ≤ Q := SimpleGraph.edgeSet_subset_edgeSet.1 hN.subset
  have := h3 Q hle hNp
  subst this
  exact hN.ne rfl
