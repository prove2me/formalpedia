-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_d5e355eb_db93_4745_85ca_eb9a9a9b0ce3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:18:56.118439+00:00
-- url     : https://prove2.me/submissions/e3829065-4834-4637-9505-0d909fca7453

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_8e19dc79_980c_4b90_a9e5_d9bf409450af_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_8e19dc79_980c_4b90_a9e5_d9bf409450af_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hLDraw, hMax⟩ :=
    WilliamsonShmoys.planar_maximal_extension__p2m_8e19dc79_980c_4b90_a9e5_d9bf409450af_a1
      K hDraw
  exact ⟨L, hKL, hLDraw,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_8e19dc79_980c_4b90_a9e5_d9bf409450af_a1
      L hLDraw hCard hMax⟩
