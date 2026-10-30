-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_e4274472_fa7f_45c2_bc46_56de2add020a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:07:39.596904+00:00
-- url     : https://prove2.me/submissions/241b54e7-cf4b-4ad9-be0a-2f4211ffeb72
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_finite_edge_maximal_extension__p2m_d847cb0d_bf38_465c_a743_e30e146fb79e_a1
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_count__p2m_d847cb0d_bf38_465c_a743_e30e146fb79e_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
      H.edgeFinset.card <= 3 * Fintype.card V - 6) := by
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hext :=
    planar_finite_edge_maximal_extension__p2m_d847cb0d_bf38_465c_a743_e30e146fb79e_a1 H hH
  cases hext with
  | intro K htail =>
    cases htail with
    | intro hsub htail =>
      cases htail with
      | intro hKplanar htail =>
        cases htail with
        | intro hcardmono hmax =>
          letI : DecidableRel K.Adj := Classical.decRel K.Adj
          have hKcount :=
            planar_maximal_edge_count__p2m_d847cb0d_bf38_465c_a743_e30e146fb79e_a1
              K hKplanar hcard hmax
          calc
            H.edgeFinset.card <= K.edgeFinset.card := hcardmono
            _ = 3 * Fintype.card V - 6 := hKcount