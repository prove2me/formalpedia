-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count__p2m_bcf9fc22_a10c_472d_8ae6_0fdb1da6c723_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:14:57.198376+00:00
-- url     : https://prove2.me/submissions/d149f547-ddd5-4e89-bd6e-b2f01590869d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_72c268f3_7cc5_487f_ad8b_d5f36984db50_a1
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_72c268f3_7cc5_487f_ad8b_d5f36984db50_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M →
      (∀ u v, L.Adj u v → M.Adj u v) →
      ∀ u v, M.Adj u v → L.Adj u v)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_72c268f3_7cc5_487f_ad8b_d5f36984db50_a1
      L hL hmax hcard
  · exact WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_72c268f3_7cc5_487f_ad8b_d5f36984db50_a1
      L hL hcard