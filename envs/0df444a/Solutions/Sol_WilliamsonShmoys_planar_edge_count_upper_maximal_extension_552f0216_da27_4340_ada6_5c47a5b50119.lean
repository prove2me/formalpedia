-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_maximal_extension_552f0216_da27_4340_ada6_5c47a5b50119
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:16:19.324195+00:00
-- url     : https://prove2.me/submissions/b774fb2d-015f-4141-b1dc-2d0565baa24d

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

theorem S185nc {V : Type} [Fintype V] {G H : SimpleGraph V} (h : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.2 h) (Set.toFinite _)
theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ H' : SimpleGraph V, H ≤ H' → WilliamsonShmoys.HasPlanarDrawingOn H' → H' = H := by
  exact S181max WilliamsonShmoys.HasPlanarDrawingOn K hK
