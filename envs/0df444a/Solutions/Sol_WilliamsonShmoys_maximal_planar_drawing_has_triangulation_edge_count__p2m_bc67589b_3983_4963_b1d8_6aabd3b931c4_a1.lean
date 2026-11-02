-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_bc67589b_3983_4963_b1d8_6aabd3b931c4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:34:46.353192+00:00
-- url     : https://prove2.me/submissions/a48dc615-e516-4425-a2f0-ca0f34c17509
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_757b64a4_4ecc_451f_8c8e_f98c58cc600e_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_757b64a4_4ecc_451f_8c8e_f98c58cc600e_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      3 * Fintype.card V = L.edgeFinset.card + 6) := by
  classical
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  have hLower :=
    WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_757b64a4_4ecc_451f_8c8e_f98c58cc600e_a1
      L hV hL hMax
  have hUpper :=
    WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_757b64a4_4ecc_451f_8c8e_f98c58cc600e_a1
      L hV hL
  omega