-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_completion__p2m_3e20b199_32f9_4aa6_83e2_00145d2a7578_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:29:01.906993+00:00
-- url     : https://prove2.me/submissions/1a7f798e-b71b-4af6-aad5-c910e1b82cb3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_49a7b880_a3f8_443f_bfbf_c306626f3a20_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_49a7b880_a3f8_443f_bfbf_c306626f3a20_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    ∃ L : SimpleGraph V, K <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      (L.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_49a7b880_a3f8_443f_bfbf_c306626f3a20_a1
      K hK
  obtain hCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_49a7b880_a3f8_443f_bfbf_c306626f3a20_a1
      L hL hMax hCard
  refine ⟨L, hKL, hL, ?_⟩
  omega