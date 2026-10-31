-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_maximal_edge_count__p2m_5aab7b66_88f9_4907_8957_a5a3c4b4addc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:32:54.255169+00:00
-- url     : https://prove2.me/submissions/d94f44e3-c506-4654-9e45-b21b4afe4020

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_bound__p2m_996f417d_299f_4de3_98ff_54d66e679a8a_a1
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation__p2m_996f417d_299f_4de3_98ff_54d66e679a8a_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ W : SimpleGraph V, U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W →
      W.edgeSet.ncard ≤ U.edgeSet.ncard) :
    U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper : U.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_graph_edge_bound__p2m_996f417d_299f_4de3_98ff_54d66e679a8a_a1 U hU hV
  obtain ⟨W, hUW, hWplanar, hWcount⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation__p2m_996f417d_299f_4de3_98ff_54d66e679a8a_a1 U hU hV
  have hWle : W.edgeSet.ncard ≤ U.edgeSet.ncard := hmax W hUW hWplanar
  have hlower : 3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by
    calc
      3 * Fintype.card V = W.edgeSet.ncard + 6 := hWcount.symm
      _ ≤ U.edgeSet.ncard + 6 := Nat.add_le_add_right hWle 6
  omega