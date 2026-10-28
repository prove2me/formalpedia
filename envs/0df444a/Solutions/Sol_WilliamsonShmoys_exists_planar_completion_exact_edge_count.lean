-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_completion_exact_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:54:22.507311+00:00
-- url     : https://prove2.me/submissions/157d219e-b100-4bc6-91be-5d1651a88b98
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_completion_a3bf2761_3b00_45d2_af0e_a4c0f6d1919f
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_a3bf2761_3b00_45d2_af0e_a4c0f6d1919f

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      (L.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_completion_a3bf2761_3b00_45d2_af0e_a4c0f6d1919f K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_edge_count_a3bf2761_3b00_45d2_af0e_a4c0f6d1919f
      L hL hMax hCard⟩
