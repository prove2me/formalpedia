-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_88aeae11_6627_4561_98a0_139448671fc8_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:46:24.25972+00:00
-- url     : https://prove2.me/submissions/5a3cb36f-08f5-4e4a-a6f0-4654d21ea985
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangulation_extension__p2m_0df19a3a_91dd_4e4b_942c_e5b79d23d807_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hn : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      letI : DecidableRel G.Adj := dG
      letI : DecidableRel K.Adj := dK
      HasPlanarDrawingOn K →
      G.edgeFinset ⊆ K.edgeFinset →
      K.edgeFinset = G.edgeFinset) :
    letI : DecidableRel G.Adj := dG
    3 * Fintype.card V - 6 ≤ G.edgeFinset.card := by
  letI : DecidableRel G.Adj := dG
  obtain ⟨K, dK, hK, hGK, hKcard⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_triangulation_extension__p2m_0df19a3a_91dd_4e4b_942c_e5b79d23d807_a1
      G dG hG hn
  letI : DecidableRel K.Adj := dK
  have hEq : K.edgeFinset = G.edgeFinset := hmax K dK hK hGK
  rw [← hEq, hKcard]
