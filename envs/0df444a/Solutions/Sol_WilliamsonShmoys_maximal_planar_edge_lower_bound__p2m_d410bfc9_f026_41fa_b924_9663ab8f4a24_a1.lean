-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_d410bfc9_f026_41fa_b924_9663ab8f4a24_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:19:41.570634+00:00
-- url     : https://prove2.me/submissions/5aa7874e-7891-4656-8054-b6cc1f738e93

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulation_completion__p2m_1d331833_450a_47b6_a107_4143d686327f_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V, M <= N -> HasPlanarDrawingOn N -> N = M) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by
  obtain ⟨H, hMH, hH, hcount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulation_completion__p2m_1d331833_450a_47b6_a107_4143d686327f_a2
      M hV hM
  have hHM : H = M := hmax H hMH hH
  rw [hHM] at hcount
  exact Nat.le_of_eq hcount.symm