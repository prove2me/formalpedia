-- Prove2me | solution 2 for WilliamsonShmoys.drawable_connected_supergraph_for_edge_bound_3daf7e3a
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:39:46.459545+00:00
-- url     : https://prove2.me/submissions/a912c9d0-a34d-4ece-8939-a0bfe7e38ac1

import Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧ Q.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn Q :=
  WilliamsonShmoys.exists_connected_planar_supergraph__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1 P hPdraw hCard
