-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_7592409d_0b44_4594_9ed9_df868002d7c4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:05:44.54786+00:00
-- url     : https://prove2.me/submissions/a80dcf25-c725-4590-aa05-226b7e58ebfc

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_extension__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bound__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_supergraph__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKconn, hKdraw⟩ :=
    WilliamsonShmoys.planar_connected_extension__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1
      H hH hV
  have hKbound :=
    WilliamsonShmoys.planar_connected_edge_bound__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1
      K hKdraw hKconn hV
  exact WilliamsonShmoys.edge_bound_of_supergraph__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1
    H K hHK hKbound