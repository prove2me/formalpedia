-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulating_supergraph__p2m_3121b121_e79f_417e_a8b9_78e91a636a8c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:20:35.128192+00:00
-- url     : https://prove2.me/submissions/30aa72c3-8aaf-4d13-ad2f-d1419597c84b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_19c64167_1c0e_4c4b_ad8b_9aac5144fe63_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_19c64167_1c0e_4c4b_ad8b_9aac5144fe63_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (T : SimpleGraph V) (dT : DecidableRel T.Adj),
      HasPlanarDrawingOn T ∧
      (letI : DecidableRel G.Adj := dG
       letI : DecidableRel T.Adj := dT
       G.edgeFinset ⊆ T.edgeFinset) ∧
      (letI : DecidableRel T.Adj := dT
       T.edgeFinset.card = 3 * Fintype.card V - 6) := by
  letI : DecidableRel G.Adj := dG
  obtain ⟨T, dT, hT, hGT, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_19c64167_1c0e_4c4b_ad8b_9aac5144fe63_a1
      G dG hG
  letI : DecidableRel T.Adj := dT
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_19c64167_1c0e_4c4b_ad8b_9aac5144fe63_a1
      T dT hT hmax hcard
  exact ⟨T, dT, hT, hGT, hcount⟩