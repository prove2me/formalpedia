-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_af412bdb_08d3_443e_9526_1f4e854292c2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:48:50.326924+00:00
-- url     : https://prove2.me/submissions/d527530a-9524-412f-aa78-561f5112da62

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_extension__p2m_8c9864f5_741a_481d_8578_325697296ee9_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨T, hMT, hTplanar, hTcount⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulated_extension__p2m_8c9864f5_741a_481d_8578_325697296ee9_a1
      M hV hM
  have hTM : T ≤ M := hmax T hMT hTplanar
  have hEq : M = T := le_antisymm hMT hTM
  cases hEq
  exact hTcount
