-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_edge_lower_bound__p2m_0cd4b9a1_dcab_4b06_b6ad_2748a36b5bdf_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T01:24:50.819022+00:00
-- url     : https://prove2.me/submissions/1e367884-e438-4463-a121-fa55a4808636
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_63ca304f_09ca_4fb0_945d_2eb65f783053_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_63ca304f_09ca_4fb0_945d_2eb65f783053_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hKdraw, hKmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_63ca304f_09ca_4fb0_945d_2eb65f783053_a2
      H hDraw
  exact ⟨K, hHK, hKdraw,
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_63ca304f_09ca_4fb0_945d_2eb65f783053_a2
      K hKdraw hKmax hV⟩