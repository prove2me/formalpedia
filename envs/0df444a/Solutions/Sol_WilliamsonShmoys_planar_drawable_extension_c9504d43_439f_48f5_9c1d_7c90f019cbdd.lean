-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_extension_c9504d43_439f_48f5_9c1d_7c90f019cbdd
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:06:21.946247+00:00
-- url     : https://prove2.me/submissions/1b829aab-08b0-49c6-b0be-ae0450ca38df

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_triangulation_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hSparse : H.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ ¬ K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  obtain ⟨K, hHK, hTri, hDraw⟩ :=
    WilliamsonShmoys.planar_drawable_triangulation_extension H hV hH
  refine ⟨K, hHK, ?_, hDraw⟩
  intro hKH
  have hEq : H = K := le_antisymm hHK hKH
  have hCount : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
    simpa [hEq] using hTri
  omega