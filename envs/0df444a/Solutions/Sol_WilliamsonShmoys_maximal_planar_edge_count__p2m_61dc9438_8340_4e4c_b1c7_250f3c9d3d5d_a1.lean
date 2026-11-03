-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_61dc9438_8340_4e4c_b1c7_250f3c9d3d5d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:59:01.286048+00:00
-- url     : https://prove2.me/submissions/ac5afac4-d931-40d2-b226-978068304404

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_sharp_edge_count__p2m_804de7f6_f862_47b4_add3_5edea203f43e_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_with_sharp_edge_count__p2m_804de7f6_f862_47b4_add3_5edea203f43e_a1
      K hcard hK
  have hLK : L <= K := hmax L hKL hL
  have hEq : K = L := le_antisymm hKL hLK
  simpa [hEq] using hcount