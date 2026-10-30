-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_strict_supergraph_of_disconnected__p2m_0d71806b_1bff_4247_911b_0bb3ff02c978_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T12:32:54.053956+00:00
-- url     : https://prove2.me/submissions/bffbbac0-c9d4-4f32-8394-1194de4e34a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count__p2m_7126cecb_c28a_4db7_af93_ede0b0cbea72_a5
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_edge_bound__p2m_7126cecb_c28a_4db7_af93_ede0b0cbea72_a5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : LE.le 3 (Fintype.card V))
    (hdis : Not H.Connected) :
    Exists fun K : SimpleGraph V =>
      And (WilliamsonShmoys.HasPlanarDrawingOn K)
        (And (Set.Subset H.edgeSet K.edgeSet)
          (Not (K.edgeSet = H.edgeSet))) := by
  obtain ⟨K, hsubset, hKdraw, hKcount⟩ :=
    WilliamsonShmoys.planar_completion_edge_count__p2m_7126cecb_c28a_4db7_af93_ede0b0cbea72_a5
      H hH hV
  have hHcount :=
    WilliamsonShmoys.disconnected_planar_edge_bound__p2m_7126cecb_c28a_4db7_af93_ede0b0cbea72_a5
      H hH hV hdis
  have hcardle : H.edgeSet.ncard ≤ K.edgeSet.ncard := Set.ncard_mono hsubset
  have hstrict : H.edgeSet.ncard < K.edgeSet.ncard := by omega
  refine ⟨K, hKdraw, hsubset, ?_⟩
  intro heq
  rw [heq] at hstrict
  omega