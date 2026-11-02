-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_edge_count_bound__p2m_75c1dbe5_597b_4ab5_bcaf_dc768f4756d8_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:30:52.025169+00:00
-- url     : https://prove2.me/submissions/1d168780-88be-457e-b099-ee4a9e0107b0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_15e1d124_3e67_41bc_8403_c26ff4c383cc_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_15e1d124_3e67_41bc_8403_c26ff4c383cc_a3

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel U.Adj := dU
     U.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨M, hUM, hM, hmax, hmono⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_15e1d124_3e67_41bc_8403_c26ff4c383cc_a3
      U dU hU
  have hcount : M.edgeFinset.card = 3 * Fintype.card V - 6 := by
    simpa using
      WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_15e1d124_3e67_41bc_8403_c26ff4c383cc_a3
        M hcard hM hmax
  have hmono' : U.edgeFinset.card ≤ M.edgeFinset.card := by
    simpa using hmono
  change U.edgeFinset.card ≤ 3 * Fintype.card V - 6
  exact hmono'.trans_eq hcount