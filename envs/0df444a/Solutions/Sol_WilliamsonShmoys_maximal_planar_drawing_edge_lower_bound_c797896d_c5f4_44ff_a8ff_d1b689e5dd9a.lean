-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_c797896d_c5f4_44ff_a8ff_d1b689e5dd9a
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:33:52.705171+00:00
-- url     : https://prove2.me/submissions/ceca6004-daa2-4e19-ae6f-35b1c05234bd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_501982a3_cf58_468c_be32_1d2a30e3e83a
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count_501982a3_cf58_468c_be32_1d2a30e3e83a

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  obtain ⟨N, hMN, hNDraw, hNMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_501982a3_cf58_468c_be32_1d2a30e3e83a
      M hDraw
  have hEq : N = M := hMax N hMN hNDraw
  have hCount :=
    WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_501982a3_cf58_468c_be32_1d2a30e3e83a
      N hV hNDraw hNMax
  rw [← hEq]
  omega