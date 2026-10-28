-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_exists_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:18:59.900327+00:00
-- url     : https://prove2.me/submissions/eb9099e2-a787-498d-ac7f-9170d6d2d31f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ G : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → G.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn G ∧
      ∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        (∀ ⦃u v : V⦄, K.Adj u v → G.Adj u v) := by 
  classical
  obtain ⟨G, hMH, hmax⟩ := Set.Finite.exists_le_maximal
    (s := {K : SimpleGraph V | WilliamsonShmoys.HasPlanarDrawingOn K}) (Set.toFinite _) hH
  exact ⟨G, fun u v h => hMH h, hmax.1, fun K hK hKp => hmax.2 hKp (fun u v h => hK h)⟩
