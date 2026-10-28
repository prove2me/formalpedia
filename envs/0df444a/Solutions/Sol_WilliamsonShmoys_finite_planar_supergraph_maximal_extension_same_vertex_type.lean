-- Prove2me | solution 1 for WilliamsonShmoys.finite_planar_supergraph_maximal_extension_same_vertex_type
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:59:41.589039+00:00
-- url     : https://prove2.me/submissions/5ed1285d-ec9d-496c-82db-8a150b30521f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V,
        N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N := by 
  classical
  obtain ⟨H, hMH, hmax⟩ := Set.Finite.exists_le_maximal
    (s := {K : SimpleGraph V | WilliamsonShmoys.HasPlanarDrawingOn K}) (Set.toFinite _) hM
  exact ⟨H, hMH, hmax.1, fun K hK hKp => hmax.2 hKp hK⟩
