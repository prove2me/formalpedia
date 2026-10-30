-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_7bfae1f5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:11:43.163507+00:00
-- url     : https://prove2.me/submissions/5eab0e09-c855-4aa1-a995-a4e2354ec83f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_planar_supergraph_maximal
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_ca2fe8f1_c3cb_4014_879e_982f2e091a93

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ W : SimpleGraph V, HasPlanarDrawingOn W ∧
      (∀ u v, G.Adj u v → W.Adj u v) ∧
      W.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨W, hW, hGW, hmax⟩ :=
    WilliamsonShmoys.drawable_planar_supergraph_maximal G hG
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_ca2fe8f1_c3cb_4014_879e_982f2e091a93 W hW hmax hCard
  exact ⟨W, hW, hGW, hcount⟩