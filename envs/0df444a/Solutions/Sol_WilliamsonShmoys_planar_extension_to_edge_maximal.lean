-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_to_edge_maximal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T11:54:01.750364+00:00
-- url     : https://prove2.me/submissions/5393207f-38cc-4e76-9aee-f1926f9b84ff

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

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.Connected ∧
      (∀ G : SimpleGraph V,
        H ≤ G → WilliamsonShmoys.HasPlanarDrawingOn G → G ≤ H) := by
  obtain ⟨H, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn K hK
  exact ⟨H, h1, h2, S185nc h1, hconn.mono h1, fun L hL hP => (h3 L hL hP).le⟩
