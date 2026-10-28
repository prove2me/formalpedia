-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_with_triangular_edge_count_maximal_e20a9b21
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:49:29.25399+00:00
-- url     : https://prove2.me/submissions/93d9e7d0-6650-414e-9019-ab4088bd52a9

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
    (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      K.edgeSet ⊆ L.edgeSet ∧
      ∀ M : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn M →
        L.edgeSet ⊆ M.edgeSet → L.edgeSet = M.edgeSet := by
  obtain ⟨L, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn K hDrawing
  exact ⟨L, h2, SimpleGraph.edgeSet_mono h1, fun M hd hL => by
    rw [h3 M (SimpleGraph.edgeSet_subset_edgeSet.1 hL) hd]⟩
