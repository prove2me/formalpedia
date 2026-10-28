-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension_same_vertices_c3c27980_9f1d_4b26_ac26_4100a7115914
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:32:30.72502+00:00
-- url     : https://prove2.me/submissions/f849daf3-c842-4d75-a532-6af5f83179fa

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
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ H : SimpleGraph V,
      R ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) ∧
      R.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, h1, h2, h3⟩ := S181max _ R hR
  exact ⟨H, h1, h2, h3, Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.2 h1) (Set.toFinite _)⟩
