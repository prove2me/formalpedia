-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_triangulation_extension__p2m_0df19a3a_91dd_4e4b_942c_e5b79d23d807_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:51:24.956482+00:00
-- url     : https://prove2.me/submissions/98b847e2-ed7b-41c1-bcec-d98f99b52d83
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_8e688b5a_4cd6_4a71_af1c_8dd5b2ac94c3_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_8e688b5a_4cd6_4a71_af1c_8dd5b2ac94c3_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      G.edgeFinset ⊆ K.edgeFinset ∧
      K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨K, dK, hKplanar, hGK, hKmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal__p2m_8e688b5a_4cd6_4a71_af1c_8dd5b2ac94c3_a1
      G dG hG hn
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_8e688b5a_4cd6_4a71_af1c_8dd5b2ac94c3_a1
      K dK hKplanar hn hKmax
  exact ⟨K, dK, hKplanar, hGK, hcount⟩