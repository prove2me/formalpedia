-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_dbf7c19f_18a9_4ddb_bdc9_64443a6c5a07_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:22:37.522058+00:00
-- url     : https://prove2.me/submissions/db33fa0a-de2e-4b0c-bddd-beba2cfb7f0e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_7a456d63_5ec6_4840_a69c_b6d30bc6b909_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_7a456d63_5ec6_4840_a69c_b6d30bc6b909_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hLmax : ∀ M : SimpleGraph V, LE.le L M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  have hupper := WilliamsonShmoys.planar_edge_upper_bound__p2m_7a456d63_5ec6_4840_a69c_b6d30bc6b909_a1 L hLplanar hV
  have hlower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7a456d63_5ec6_4840_a69c_b6d30bc6b909_a1 L hLplanar hV hLmax
  omega