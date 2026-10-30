-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion_exact_edge_count__p2m_70a6424f_4889_4ef2_870f_ee6e7e607f96_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:32:01.305622+00:00
-- url     : https://prove2.me/submissions/df964573-1c5d-4b2f-8b82-37010cef8c1f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_2cd3ad17_4dba_4e7e_aee4_3660ec319d01_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_2cd3ad17_4dba_4e7e_aee4_3660ec319d01_a1
import Mathlib
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_2cd3ad17_4dba_4e7e_aee4_3660ec319d01_a1
      K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_2cd3ad17_4dba_4e7e_aee4_3660ec319d01_a1
      L hV hL hmax⟩