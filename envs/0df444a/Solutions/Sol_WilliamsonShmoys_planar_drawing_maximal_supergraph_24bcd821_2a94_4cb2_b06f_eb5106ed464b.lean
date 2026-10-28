-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph_24bcd821_2a94_4cb2_b06f_eb5106ed464b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T08:48:25.388835+00:00
-- url     : https://prove2.me/submissions/98a06bb2-f935-440f-9e7b-c93f502d361a

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
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        M.edgeSet ⊂ N.edgeSet → ¬ WilliamsonShmoys.HasPlanarDrawingOn N := by
  obtain ⟨M, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn L hL
  refine ⟨M, SimpleGraph.edgeSet_subset_edgeSet.2 h1, h2, fun N hN hNp => ?_⟩
  have hle : M ≤ N := SimpleGraph.edgeSet_subset_edgeSet.1 hN.subset
  have := h3 N hle hNp
  subst this
  exact hN.ne rfl
