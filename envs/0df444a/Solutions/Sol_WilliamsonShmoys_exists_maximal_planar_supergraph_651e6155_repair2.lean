-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_651e6155_repair2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:09:36.875198+00:00
-- url     : https://prove2.me/submissions/7997bbd6-5914-4f00-8550-140e5c02724f

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
    (L : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L.edgeSet ⊆ M.edgeSet ∧
      (∀ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N →
        M.edgeSet ⊆ N.edgeSet → N.edgeSet = M.edgeSet) := by
  obtain ⟨M, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn L hDrawing
  exact ⟨M, h2, SimpleGraph.edgeSet_mono h1, fun N hd hL => by
    rw [h3 N (SimpleGraph.edgeSet_subset_edgeSet.1 hL) hd]⟩
