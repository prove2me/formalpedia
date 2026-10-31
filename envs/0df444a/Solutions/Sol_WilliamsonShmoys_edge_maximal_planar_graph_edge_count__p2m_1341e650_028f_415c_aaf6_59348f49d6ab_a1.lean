-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_edge_count__p2m_1341e650_028f_415c_aaf6_59348f49d6ab_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:41:16.876019+00:00
-- url     : https://prove2.me/submissions/195e93df-f8c3-489f-94f9-8895b55dbe03

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_exact_edge_count__p2m_ec616bf2_f49f_4c75_9fdb_bf987c0ab16b_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hKN, hN, hCount⟩ :=
    WilliamsonShmoys.planar_completion_exact_edge_count__p2m_ec616bf2_f49f_4c75_9fdb_bf987c0ab16b_a1
      K hV hK
  have hNK : N.edgeSet ⊆ K.edgeSet := hMax N hKN hN
  have hEdges : K.edgeSet = N.edgeSet := Set.Subset.antisymm hKN hNK
  rw [hEdges]
  exact hCount