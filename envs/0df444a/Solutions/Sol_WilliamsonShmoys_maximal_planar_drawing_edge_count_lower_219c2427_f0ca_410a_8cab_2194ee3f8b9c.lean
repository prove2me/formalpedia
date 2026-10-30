-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_219c2427_f0ca_410a_8cab_2194ee3f8b9c
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:58:43.171981+00:00
-- url     : https://prove2.me/submissions/fe92e6a5-56b2-45e3-a3dc-129477e07481

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_lower_bound_78919b52_de37_4426_ade1_0aaa5522d1e4

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  classical
  obtain ⟨L, hKL, hL, hLower⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_edge_lower_bound_78919b52_de37_4426_ade1_0aaa5522d1e4 K hK hCard
  have hLK : L <= K := hMax L hKL hL
  have hEdges : L.edgeSet.ncard <= K.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hLK)
  exact le_trans hLower (Nat.add_le_add_right hEdges 6)