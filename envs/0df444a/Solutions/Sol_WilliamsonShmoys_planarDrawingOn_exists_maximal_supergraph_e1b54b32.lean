-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_exists_maximal_supergraph_e1b54b32
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:27:56.205951+00:00
-- url     : https://prove2.me/submissions/cecc428a-1ad7-4751-b9e2-77b24ca4f559

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
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V,
        N.edgeSet ⊂ P.edgeSet → ¬ WilliamsonShmoys.HasPlanarDrawingOn P := by
  obtain ⟨N0, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn M hM
  refine ⟨N0, SimpleGraph.edgeSet_subset_edgeSet.2 h1, h2, fun N hN hNp => ?_⟩
  have hle : N0 ≤ N := SimpleGraph.edgeSet_subset_edgeSet.1 hN.subset
  have := h3 N hle hNp
  subst this
  exact hN.ne rfl
