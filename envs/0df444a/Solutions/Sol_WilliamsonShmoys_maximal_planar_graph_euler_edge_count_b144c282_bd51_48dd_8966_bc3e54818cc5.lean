-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_euler_edge_count_b144c282_bd51_48dd_8966_bc3e54818cc5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:35:11.023489+00:00
-- url     : https://prove2.me/submissions/5b45e15c-48dc-4cec-977e-cad68a1c8404

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_euler_edge_count_b144c282_bd51_48dd_8966_bc3e54818cc5_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_euler_edge_count_b144c282_bd51_48dd_8966_bc3e54818cc5_strict_augmentation

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      L.edgeSet ⊆ M.edgeSet ->
      M.edgeSet ⊆ L.edgeSet) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper :
      L.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
    WilliamsonShmoys.maximal_planar_graph_euler_edge_count_b144c282_bd51_48dd_8966_bc3e54818cc5_upper_bound
      L hL hV
  have hlower :
      3 * Fintype.card V <= L.edgeSet.ncard + 6 := by
    by_contra h
    have hsparse :
        L.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
    obtain ⟨M, hM, hsub, hnot⟩ :=
      WilliamsonShmoys.maximal_planar_graph_euler_edge_count_b144c282_bd51_48dd_8966_bc3e54818cc5_strict_augmentation
        L hL hV hsparse
    exact hnot (hmax M hM hsub)
  omega