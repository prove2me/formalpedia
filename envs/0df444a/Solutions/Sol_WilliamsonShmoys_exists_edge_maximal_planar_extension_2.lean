-- Prove2me | solution 2 for WilliamsonShmoys.exists_edge_maximal_planar_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:31:47.78915+00:00
-- url     : https://prove2.me/submissions/8981b263-be09-4b63-8541-1b9a20278bd9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L := by 
  classical
  obtain ⟨H, hKH, hmax⟩ := Finite.exists_le_maximal
    (p := fun K : SimpleGraph V => WilliamsonShmoys.HasPlanarDrawingOn K) hK
  exact ⟨H, hKH, hmax.1, fun M h hM => hmax.2 hM h⟩
