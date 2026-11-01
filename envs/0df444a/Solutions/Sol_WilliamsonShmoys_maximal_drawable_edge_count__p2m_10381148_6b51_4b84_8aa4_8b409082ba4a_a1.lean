-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_10381148_6b51_4b84_8aa4_8b409082ba4a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:23:46.0382+00:00
-- url     : https://prove2.me/submissions/b23bd535-101a-4421-b377-171d10cc923e

import Theorems.Thm_WilliamsonShmoys_planar_graph_extends_to_triangulation__p2m_1011a2ca_0dda_4069_a6bc_e4d75ecb3269_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L = K) :
    3 * Fintype.card V - 6 = K.edgeSet.ncard := by
  obtain ⟨L, hsub, hL, hcount⟩ :=
    WilliamsonShmoys.planar_graph_extends_to_triangulation__p2m_1011a2ca_0dda_4069_a6bc_e4d75ecb3269_a1
      K hcard hK
  have hLK : L = K := hmax L hsub hL
  calc
    3 * Fintype.card V - 6 = L.edgeSet.ncard := hcount.symm
    _ = K.edgeSet.ncard := congrArg (fun G : SimpleGraph V => G.edgeSet.ncard) hLK