-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_supergraph__p2m_11b8d141_5db8_4e85_8178_19adf7dd7abd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:32:51.592981+00:00
-- url     : https://prove2.me/submissions/a9b0b4b8-3dad-4260-ae1e-830a3008d46f

import Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph_of_drawing__p2m_5438d717_60ba_4719_bd8d_a39b0e45c967_a4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard :=
  WilliamsonShmoys.connected_planar_supergraph_of_drawing__p2m_5438d717_60ba_4719_bd8d_a39b0e45c967_a4 K hK hV
