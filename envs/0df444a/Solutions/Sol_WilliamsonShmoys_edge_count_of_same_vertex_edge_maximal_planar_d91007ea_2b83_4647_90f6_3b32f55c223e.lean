-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_same_vertex_edge_maximal_planar_d91007ea_2b83_4647_90f6_3b32f55c223e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:42:56.043619+00:00
-- url     : https://prove2.me/submissions/116902f5-4c29-47d1-8e46-6c68d3ddfec3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_3b82d126
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_3b82d126

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      (∀ ⦃u v⦄, K.Adj u v → M.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      ∀ ⦃u v⦄, M.Adj u v → K.Adj u v) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound_3b82d126 K hK hV
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_3b82d126 K hK hV hmax
  omega