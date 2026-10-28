-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_edge_maximal_planar_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:13:05.202961+00:00
-- url     : https://prove2.me/submissions/7e97bdf7-ffbc-4a94-8f1e-498f828fc9b2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by 
  classical
  obtain ⟨H, hGH, hmax⟩ := Finite.exists_le_maximal
    (p := fun K : SimpleGraph V => WilliamsonShmoys.HasPlanarDrawingOn K) hG
  exact ⟨H, hGH, hmax.1, fun L hHL hL => le_antisymm (hmax.2 hL hHL) hHL⟩
