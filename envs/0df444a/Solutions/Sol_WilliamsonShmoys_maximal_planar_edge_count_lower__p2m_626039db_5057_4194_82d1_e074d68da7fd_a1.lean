-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_626039db_5057_4194_82d1_e074d68da7fd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:16:50.786645+00:00
-- url     : https://prove2.me/submissions/7187ce33-49db-49b8-8ae3-f89d0777766c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulating_supergraph__p2m_3121b121_e79f_417e_a8b9_78e91a636a8c_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ (G : SimpleGraph V) (dG : DecidableRel G.Adj),
      HasPlanarDrawingOn G →
      (letI : DecidableRel H.Adj := dH
       letI : DecidableRel G.Adj := dG
       H.edgeFinset ⊆ G.edgeFinset → H.edgeFinset = G.edgeFinset))
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel H.Adj := dH
     3 * Fintype.card V - 6 ≤ H.edgeFinset.card) := by
  letI : DecidableRel H.Adj := dH
  obtain ⟨T, dT, hT, hsub, htight⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulating_supergraph__p2m_3121b121_e79f_417e_a8b9_78e91a636a8c_a1
      H dH hH hcard
  letI : DecidableRel T.Adj := dT
  have heq : H.edgeFinset = T.edgeFinset := hmax T dT hT hsub
  have hcardEq : H.edgeFinset.card = T.edgeFinset.card := congrArg Finset.card heq
  rw [htight] at hcardEq
  omega