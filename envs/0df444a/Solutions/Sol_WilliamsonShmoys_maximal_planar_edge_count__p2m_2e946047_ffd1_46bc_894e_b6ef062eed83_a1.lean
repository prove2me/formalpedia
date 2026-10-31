-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_2e946047_ffd1_46bc_894e_b6ef062eed83_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:49:00.080918+00:00
-- url     : https://prove2.me/submissions/5853f150-b87b-4e7b-a5aa-b353ab13c6bd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_630b5c25_00a7_4258_a685_bfcae7eacbce_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_630b5c25_00a7_4258_a685_bfcae7eacbce_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_630b5c25_00a7_4258_a685_bfcae7eacbce_a2 M hM hV
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_630b5c25_00a7_4258_a685_bfcae7eacbce_a2 M hM hV hmax
  omega