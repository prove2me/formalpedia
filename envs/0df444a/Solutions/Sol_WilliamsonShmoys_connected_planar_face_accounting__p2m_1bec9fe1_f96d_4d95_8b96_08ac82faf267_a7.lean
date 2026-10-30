-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_face_accounting__p2m_1bec9fe1_f96d_4d95_8b96_08ac82faf267_a7
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:23:10.467982+00:00
-- url     : https://prove2.me/submissions/1a837a5b-85f4-4359-b8e4-b193520abba9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_87f8bddb_6da2_4d95_81aa_1f835ee1c5bb_a3

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hConn : N.Connected) (hDraw : HasPlanarDrawingOn N) :
    ∃ f : Int,
      (Fintype.card V : Int) - (N.edgeSet.ncard : Int) + f = 2 ∧
      3 * f ≤ 2 * (N.edgeSet.ncard : Int) := by
  have hE := WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_87f8bddb_6da2_4d95_81aa_1f835ee1c5bb_a3
    N hV hConn hDraw
  refine ⟨(N.edgeSet.ncard : Int) - (Fintype.card V : Int) + 2, ?_, ?_⟩
  · omega
  · omega