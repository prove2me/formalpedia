-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_finite_maximal_extension_ws
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:16:18.548623+00:00
-- url     : https://prove2.me/submissions/da2937fa-6efd-4962-b9b8-7a2836ff2c28

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
theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L := by
  obtain ⟨L, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn K hK
  exact ⟨L, h1, h2, fun M hM hP => (h3 M hM hP).le⟩
