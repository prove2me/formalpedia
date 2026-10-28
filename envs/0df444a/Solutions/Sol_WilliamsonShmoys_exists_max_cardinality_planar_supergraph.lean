-- Prove2me | solution 1 for WilliamsonShmoys.exists_max_cardinality_planar_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:07:51.460449+00:00
-- url     : https://prove2.me/submissions/4db02b65-2000-4dc0-9575-ca94037aae92

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, N ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard := by 
  classical
  obtain ⟨M, hM, hmax⟩ := Set.exists_max_image
    {K : SimpleGraph V | N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K}
    (fun K => K.edgeSet.ncard) (Set.toFinite _) ⟨N, le_rfl, hN⟩
  exact ⟨M, hM.1, hM.2, fun L h1 h2 => hmax L ⟨h1, h2⟩⟩
