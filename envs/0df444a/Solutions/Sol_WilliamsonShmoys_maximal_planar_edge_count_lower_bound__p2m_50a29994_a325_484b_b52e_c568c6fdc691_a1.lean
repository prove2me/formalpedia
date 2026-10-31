-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_50a29994_a325_484b_b52e_c568c6fdc691_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:57:38.364519+00:00
-- url     : https://prove2.me/submissions/2eb0546d-4706-4590-8efd-6114cd400056

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_exact__p2m_873dde20_79e9_4f77_962d_78285a200769_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hMax : ∀ U : SimpleGraph V, T ≤ U →
      WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by
  exact le_of_eq
    (WilliamsonShmoys.maximal_planar_edge_count_exact__p2m_873dde20_79e9_4f77_962d_78285a200769_a1
      T hV hDraw hMax)