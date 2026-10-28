-- Prove2me | solution 2 for WilliamsonShmoys.exists_maximal_planar_extension_for_triangulated_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:38:45.477783+00:00
-- url     : https://prove2.me/submissions/789c9d78-cb67-4f73-b998-8c6db9c47af9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false
theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by 
  classical
  obtain ⟨H, hMH, hmax⟩ := Finite.exists_le_maximal
    (p := fun K : SimpleGraph V => WilliamsonShmoys.HasPlanarDrawingOn K) (by assumption)
  exact ⟨H, hMH, hmax.1, fun M hM hMp => le_antisymm (hmax.2 hMp hM) hM⟩
