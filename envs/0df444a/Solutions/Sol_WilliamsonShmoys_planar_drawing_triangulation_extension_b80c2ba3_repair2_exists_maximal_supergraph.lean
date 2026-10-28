-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_b80c2ba3_repair2_exists_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:32:32.947118+00:00
-- url     : https://prove2.me/submissions/b1774f17-57aa-4074-94da-bc6fc3149284

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
    (M : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet ⊆ N.edgeSet ∧
      ∀ P : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn P →
        N.edgeSet ⊆ P.edgeSet →
        P.edgeSet ⊆ N.edgeSet := by
  obtain ⟨N, h1, h2, h3⟩ := S181max _ M hDrawing
  refine ⟨N, h2, SimpleGraph.edgeSet_subset_edgeSet.2 h1, fun P hP hs => ?_⟩
  rw [h3 P (SimpleGraph.edgeSet_subset_edgeSet.1 hs) hP]
