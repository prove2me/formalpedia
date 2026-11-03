-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_b901b325_be9f_472f_92a1_3f9f2725a3e6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:26:32.917994+00:00
-- url     : https://prove2.me/submissions/04efc56d-fa71-4a55-b9c1-a59b693cb09b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_exact_edge_count__p2m_f879e044_377f_46b9_9503_40e9e2d9cd50_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V, M <= N -> HasPlanarDrawingOn N -> N = M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
     M.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  classical
  have hex := WilliamsonShmoys.planar_triangulation_extension_exact_edge_count__p2m_f879e044_377f_46b9_9503_40e9e2d9cd50_a1
      M hV hM
  cases hex with
  | intro N hex =>
    cases hex with
    | intro hMN hex =>
      cases hex with
      | intro hN hcount =>
        have hEq : N = M := hmax N hMN hN
        subst N
        simpa using hcount