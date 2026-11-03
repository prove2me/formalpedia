-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_834425e9_b96f_42af_82f3_183711eb71b2_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:48:10.106993+00:00
-- url     : https://prove2.me/submissions/e562de65-b17e-4874-9d69-535bef3846ac

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_equations__p2m_6a93ee10_5962_45c7_890c_230c5f08b7cb_a4

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    3 * Fintype.card V - 6 <= L.edgeFinset.card := by
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_equations__p2m_6a93ee10_5962_45c7_890c_230c5f08b7cb_a4
      L hL hmax hcard
  omega