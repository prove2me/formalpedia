-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_bb4dce47_9275_45c5_899b_6355cecbb075_a5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T02:55:53.918993+00:00
-- url     : https://prove2.me/submissions/5048b24d-3e68-450b-88f9-1b0606fc2e28

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_nat_bound__p2m_de6b6dff_c710_4528_88b6_44a74b62cc1d_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_nat_bound__p2m_de6b6dff_c710_4528_88b6_44a74b62cc1d_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hconn : H.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hu := WilliamsonShmoys.planar_edge_count_upper_nat_bound__p2m_de6b6dff_c710_4528_88b6_44a74b62cc1d_a2 H hdraw hCard
  have hl := WilliamsonShmoys.maximal_planar_edge_count_lower_nat_bound__p2m_de6b6dff_c710_4528_88b6_44a74b62cc1d_a2 H hconn hdraw hCard hmax
  exact Nat.le_antisymm hu hl