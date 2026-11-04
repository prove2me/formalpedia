-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_757b64a4_4ecc_451f_8c8e_f98c58cc600e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:47:41.989445+00:00
-- url     : https://prove2.me/submissions/732eca2e-151d-460d-ae53-9d14f5ac0214

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_711cef84_2190_482b_bc2d_a11a812cbece_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_711cef84_2190_482b_bc2d_a11a812cbece_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      L.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  obtain ⟨H, hH, hle, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_extension__p2m_711cef84_2190_482b_bc2d_a11a812cbece_a1 L hL
  have heq := WilliamsonShmoys.maximal_planar_edge_count__p2m_711cef84_2190_482b_bc2d_a11a812cbece_a1 H hV hH hmax
  omega
