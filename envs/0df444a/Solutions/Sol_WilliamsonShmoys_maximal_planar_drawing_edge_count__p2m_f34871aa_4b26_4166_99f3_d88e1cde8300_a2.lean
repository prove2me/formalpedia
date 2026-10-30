-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_f34871aa_4b26_4166_99f3_d88e1cde8300_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:14:07.619001+00:00
-- url     : https://prove2.me/submissions/dd0cf5a8-8ba3-400a-9e18-882ef379e359

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_completion__p2m_3e20b199_32f9_4aa6_83e2_00145d2a7578_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K <= L → WilliamsonShmoys.HasPlanarDrawingOn L → L <= K) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨L, hKL, hL, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulated_completion__p2m_3e20b199_32f9_4aa6_83e2_00145d2a7578_a1
      K hK hCard
  have hLK : L <= K := hMax L hKL hL
  have hEq : K = L := le_antisymm hKL hLK
  rw [hEq]
  exact hCount