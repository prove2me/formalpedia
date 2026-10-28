-- Prove2me | solution 2 for WilliamsonShmoys.connected_supergraph_of_planar_bridge_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:32:05.037816+00:00
-- url     : https://prove2.me/submissions/697f082d-383c-4c63-8f3b-a1cb3998ea3d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (bridge_extension : ∀ (K : SimpleGraph V),
      WilliamsonShmoys.HasPlanarDrawingOn K →
      ¬ (∀ u v : V, Nonempty (K.Walk u v)) →
      ∃ L : SimpleGraph V,
        K ≤ L ∧
        WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∃ u v : V, ¬ Nonempty (K.Walk u v) ∧ L.Adj u v) :
    ∃ H : SimpleGraph V,
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ u v : V, Nonempty (H.Walk u v)) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by 
  classical
  obtain ⟨H, hKH, hmax⟩ := Finite.exists_le_maximal
    (p := fun K : SimpleGraph V => WilliamsonShmoys.HasPlanarDrawingOn K) hG
  refine ⟨H, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hKH) (Set.toFinite _), ?_, hmax.1⟩
  by_contra hc
  obtain ⟨L, hHL, hPL, u, v, huv, hL⟩ := bridge_extension H hmax.1 hc
  exact huv ⟨(hmax.2 hPL hHL hL).toWalk⟩
