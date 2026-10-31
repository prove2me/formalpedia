-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulated_supergraph__p2m_3a9c85e5_093c_48f7_b644_f83c4d4db2f4_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:06:41.446764+00:00
-- url     : https://prove2.me/submissions/404578df-1560-4de9-894f-49bea2e660ad

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_b8d35c99_ccc1_4cae_8065_458ad4737ca1_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_b8d35c99_ccc1_4cae_8065_458ad4737ca1_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    Exists fun K : SimpleGraph V => G <= K /\ HasPlanarDrawingOn K /\
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_b8d35c99_ccc1_4cae_8065_458ad4737ca1_a1
      G hG
  have hcount :=
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_b8d35c99_ccc1_4cae_8065_458ad4737ca1_a1
      K hV hK hmax
  exact Exists.intro K (And.intro hGK (And.intro hK hcount))