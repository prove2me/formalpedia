-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_e972185b_4990_47b3_b33a_686d33f273ec_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:29:28.262099+00:00
-- url     : https://prove2.me/submissions/34203d4b-1453-4d1e-bf11-e6fe2da851e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_augmentation__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
      H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  obtain ⟨K, hHK, hKdraw, hKmax, hcard⟩ :=
    WilliamsonShmoys.maximal_planar_augmentation__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a2
      H hH hV
  have hKbound :=
    WilliamsonShmoys.maximal_planar_edge_bound__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a2
      K hV hKdraw hKmax
  omega