-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_triangulation_extension_baad2582_408f_4cf5_91c1_4db79dadb6d2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:58:47.269656+00:00
-- url     : https://prove2.me/submissions/2c4d9e9d-92bc-462c-aac0-2e84b5e90d98
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_finite_edge_max_20261027
import Theorems.Thm_WilliamsonShmoys_planar_drawing_max_edge_euler_20261027
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_euler_finite_edge_max_20261027 K hK
  refine ⟨L, hKL, hL, ?_⟩
  apply WilliamsonShmoys.planar_drawing_max_edge_euler_20261027 L hV hL
  intro M hLM hM
  exact hMax M (le_trans hKL hLM) hM