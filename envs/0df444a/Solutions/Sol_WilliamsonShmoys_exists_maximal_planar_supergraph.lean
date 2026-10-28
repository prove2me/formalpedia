-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:34:44.549146+00:00
-- url     : https://prove2.me/submissions/22b8689e-d3ea-42be-8543-930de17b23d5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ H : SimpleGraph V,
        (∀ ⦃u v : V⦄, K.Adj u v → H.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn H →
        H.edgeSet.ncard ≤ K.edgeSet.ncard := by 
  classical
  obtain ⟨K, hGK, hmax⟩ := Finite.exists_le_maximal
    (p := fun K : SimpleGraph V => WilliamsonShmoys.HasPlanarDrawingOn K) hG
  refine ⟨K, fun u v h => hGK h, hmax.1, fun H hKH hH => ?_⟩
  have h1 : K ≤ H := fun u v h => hKH h
  rw [le_antisymm (hmax.2 hH h1) h1]
