-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_f665013f_6016_4c73_b421_fe3c911da6bd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:11:31.72639+00:00
-- url     : https://prove2.me/submissions/f8f9e8f0-f466-41c1-8045-531f80f500b4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_upper_bound__p2m_742e15ee_6999_43aa_960c_9e8cbc35dbfd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_742e15ee_6999_43aa_960c_9e8cbc35dbfd_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V)
    (hMax : forall K : SimpleGraph V, M <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.maximal_planar_drawing_edge_count_upper_bound__p2m_742e15ee_6999_43aa_960c_9e8cbc35dbfd_a1 M hM hV
  have hlower := WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_742e15ee_6999_43aa_960c_9e8cbc35dbfd_a1 M hM hV hMax
  omega