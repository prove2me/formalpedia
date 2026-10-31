-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_db367b77_db98_427b_b1c6_513aa1e72eeb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:20:10.155236+00:00
-- url     : https://prove2.me/submissions/b3cfa9c5-a89d-411f-ba5a-80b343ed3e73

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_b1f3c834_8744_4db6_8afe_73efa3792eac_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_b1f3c834_8744_4db6_8afe_73efa3792eac_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hDraw : HasPlanarDrawingOn P)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q → Q ≤ P) :
    P.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hup :=
    WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_b1f3c834_8744_4db6_8afe_73efa3792eac_a1
      P hDraw hV
  have hlo :=
    WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_b1f3c834_8744_4db6_8afe_73efa3792eac_a1
      P hDraw hV hMax
  omega