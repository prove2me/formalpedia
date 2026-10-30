-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_0869a5fc_4e7b_4b4a_9c67_2dc00ff9ed2f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:37:52.017759+00:00
-- url     : https://prove2.me/submissions/175a1063-9115-4243-9297-993a42ae5722
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_completion_exact_edge_count__p2m_85349ab1_c6ef_46c3_ac33_c15eeda728ae_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hU : HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V, U.edgeSet ⊆ W.edgeSet →
      HasPlanarDrawingOn W → U.edgeSet = W.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ U.edgeSet.ncard := by
  obtain ⟨H, hUH, hH, hEdges⟩ :=
    WilliamsonShmoys.planar_completion_exact_edge_count__p2m_85349ab1_c6ef_46c3_ac33_c15eeda728ae_a2
      U hU hV
  have hEq : U.edgeSet = H.edgeSet := hmax H hUH hH
  rw [hEq]
  exact le_of_eq hEdges.symm