-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_edgeMaximal_extension_5fac830d_330a_4033_b92d_b2d1f0f7b487
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:20:10.389138+00:00
-- url     : https://prove2.me/submissions/5b46c7bd-57df-4ce1-bd76-e23dc31dc43b

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
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      N ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ K : SimpleGraph V,
        M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ M) ∧
      N.edgeSet.ncard ≤ M.edgeSet.ncard := by
  obtain ⟨H, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn N hN
  exact ⟨H, h1, h2, fun L hL hQ => (h3 L hL hQ).le,
    Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.2 h1) (Set.toFinite _)⟩
