-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_f9dc181e_d230_4644_be1b_965b4f83a602_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:05:52.701902+00:00
-- url     : https://prove2.me/submissions/b80004ca-3984-4ffd-8d03-908f03c6b86b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_extension__p2m_f64d1837_5003_4948_9974_ab50e71d546a_a2
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : LE.le 3 (Fintype.card V)) :
    LE.le (K.edgeSet.ncard + 6) (3 * Fintype.card V) := by
  obtain ⟨H, hKH, _hH, hHcard⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulation_extension__p2m_f64d1837_5003_4948_9974_ab50e71d546a_a2
      K hK hV
  have hcard : K.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_mono hKH
  omega