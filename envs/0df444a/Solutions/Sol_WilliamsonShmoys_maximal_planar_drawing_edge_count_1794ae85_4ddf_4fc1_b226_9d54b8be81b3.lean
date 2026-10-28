-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_1794ae85_4ddf_4fc1_b226_9d54b8be81b3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T14:01:23.008967+00:00
-- url     : https://prove2.me/submissions/6e425d92-2690-461b-9acd-9d0d7e1e32d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_upper_bound_1794ae85_4ddf_4fc1_b226_9d54b8be81b3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_1794ae85_4ddf_4fc1_b226_9d54b8be81b3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper :=
    WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound_1794ae85_4ddf_4fc1_b226_9d54b8be81b3
      M hM hCard
  have hLower :=
    WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_1794ae85_4ddf_4fc1_b226_9d54b8be81b3
      M hM hCard hMax
  omega