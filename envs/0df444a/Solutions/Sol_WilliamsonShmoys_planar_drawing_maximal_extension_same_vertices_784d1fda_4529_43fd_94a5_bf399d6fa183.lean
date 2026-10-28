-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_same_vertices_784d1fda_4529_43fd_94a5_bf399d6fa183
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:25:48.8332+00:00
-- url     : https://prove2.me/submissions/6a0918a9-e6be-41de-a7b2-87bf1d1f853a

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
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    Exists (fun M : SimpleGraph V =>
      And (P.edgeSet ⊆ M.edgeSet)
      (And (WilliamsonShmoys.HasPlanarDrawingOn M)
        (forall R : SimpleGraph V,
          M.edgeSet ⊆ R.edgeSet ->
          WilliamsonShmoys.HasPlanarDrawingOn R ->
          R.edgeSet = M.edgeSet))) := by
  obtain ⟨M, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn P hP
  refine ⟨M, SimpleGraph.edgeSet_subset_edgeSet.2 h1, h2, fun R hR hPR => ?_⟩
  rw [h3 R (SimpleGraph.edgeSet_subset_edgeSet.1 hR) hPR]
