-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_upper_bound_finite_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:17:39.586854+00:00
-- url     : https://prove2.me/submissions/e5efc6f0-3308-40b5-aaf4-25b716c69bc2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ K' : SimpleGraph V, K ≤ K' →
        WilliamsonShmoys.HasPlanarDrawingOn K' → K' = K) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by 
  classical
  obtain ⟨K, hMH, hmax⟩ := Set.Finite.exists_le_maximal
    (s := {K : SimpleGraph V | WilliamsonShmoys.HasPlanarDrawingOn K}) (Set.toFinite _) hH
  exact ⟨K, hMH, hmax.1, fun K' hK hKp => le_antisymm (hmax.2 hKp hK) hK,
    Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hMH) (Set.toFinite _)⟩
