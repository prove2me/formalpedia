-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:06:56.710065+00:00
-- url     : https://prove2.me/submissions/2b329f82-4b9d-43f0-8616-48d20271a721

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, K.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ G : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → G.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn G → G = H) := by 
  classical
  obtain ⟨H, hMH, hmax⟩ := Set.Finite.exists_le_maximal
    (s := {K : SimpleGraph V | WilliamsonShmoys.HasPlanarDrawingOn K}) (Set.toFinite _) hK
  exact ⟨H, fun u v h => hMH h, hmax.1, fun G hG hGp => le_antisymm (hmax.2 hGp (fun u v h => hG h)) (fun u v h => hG h)⟩
