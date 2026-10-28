-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_strict_extension_below_bound_ce5c260b_bd9c_4523_ad2e_2ffb5e12904c
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:37:07.381984+00:00
-- url     : https://prove2.me/submissions/1b49e84e-113b-4100-a691-bef814f93d70
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_maximalExtension
import Theorems.Thm_WilliamsonShmoys_planarDrawing_saturated_edge_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N)
    (hCard : 3 <= Fintype.card V)
    (hSmall : N.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ P : SimpleGraph V, N ≤ P ∧ P ≠ N ∧ HasPlanarDrawingOn P := by
  obtain ⟨P, hNP, hP, hMax⟩ :=
    WilliamsonShmoys.planarDrawing_maximalExtension N hN
  have hBound :=
    WilliamsonShmoys.planarDrawing_saturated_edge_bound P hP hCard hMax
  have hPN : P ≠ N := by
    intro hEq
    have hBoundN : 3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by
      simpa [hEq] using hBound
    omega
  exact ⟨P, hNP, hPN, hP⟩