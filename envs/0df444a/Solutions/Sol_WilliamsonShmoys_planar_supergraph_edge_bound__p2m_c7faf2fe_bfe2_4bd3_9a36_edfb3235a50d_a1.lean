-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_bound__p2m_c7faf2fe_bfe2_4bd3_9a36_edfb3235a50d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:08:38.060653+00:00
-- url     : https://prove2.me/submissions/ce9fd9a8-04e0-4132-b873-4b589dd30fdf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_a35190bf_fe1a_4d87_ab3a_82a6067f7e12_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_a35190bf_fe1a_4d87_ab3a_82a6067f7e12_a1
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : LE.le 3 (Fintype.card V)) :
    ∃ L : SimpleGraph V,
      LE.le K L ∧
      HasPlanarDrawingOn L ∧
      LE.le (3 * Fintype.card V) (L.edgeSet.ncard + 6) := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_a35190bf_fe1a_4d87_ab3a_82a6067f7e12_a1
      K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_edge_bound__p2m_a35190bf_fe1a_4d87_ab3a_82a6067f7e12_a1
      L hL hV hmax⟩