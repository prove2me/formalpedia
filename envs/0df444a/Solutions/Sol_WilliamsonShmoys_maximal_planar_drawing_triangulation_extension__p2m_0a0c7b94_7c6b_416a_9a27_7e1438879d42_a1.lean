-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_triangulation_extension__p2m_0a0c7b94_7c6b_416a_9a27_7e1438879d42_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:39:21.034628+00:00
-- url     : https://prove2.me/submissions/674d63d5-23e4-4ad3-9ce6-37adaae8720e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_dee0ca40_6c9c_434d_8ef7_a3ab7a09b0fc_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_dee0ca40_6c9c_434d_8ef7_a3ab7a09b0fc_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hR : HasPlanarDrawingOn R) :
    ∃ T : SimpleGraph V, R ≤ T ∧ HasPlanarDrawingOn T ∧
      (letI : DecidableRel T.Adj := Classical.decRel T.Adj
       3 * Fintype.card V = T.edgeFinset.card + 6) := by
  obtain ⟨M, hRM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_dee0ca40_6c9c_434d_8ef7_a3ab7a09b0fc_a1 R hR
  refine ⟨M, hRM, hM, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_dee0ca40_6c9c_434d_8ef7_a3ab7a09b0fc_a1 M hV hM hmax