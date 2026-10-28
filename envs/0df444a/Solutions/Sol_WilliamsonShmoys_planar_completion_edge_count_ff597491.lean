-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_edge_count_ff597491
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:48:03.183276+00:00
-- url     : https://prove2.me/submissions/4fa4c42b-70fa-43c0-9371-6041bc82e6a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_finite_v2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_euler_v2
set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V, G <= H ∧ HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_extension_finite_v2 G hG
  exact ⟨H, hGH, hH,
    WilliamsonShmoys.maximal_planar_edge_count_euler_v2 H hH hmax hCard⟩