-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_single_edge_extension__p2m_c8d20c40_a498_43d8_b4ed_abd0723d73a4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:52:25.473279+00:00
-- url     : https://prove2.me/submissions/fbc9f666-33b8-4632-9113-50c0a0c2ffac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_component_cut__p2m_bde12a09_c3ff_49b5_827a_2421e10fc278_a1
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_glue_bridge__p2m_bde12a09_c3ff_49b5_827a_2421e10fc278_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (u v : V)
    (hdisj : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ a b, H.Adj a b ↔
        G.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u)) := by
  obtain ⟨S, A, B, huS, hvS, hsplit, hAs, hBs, hAplanar, hBplanar⟩ :=
    WilliamsonShmoys.planarDrawingOn_component_cut__p2m_bde12a09_c3ff_49b5_827a_2421e10fc278_a1
      G hG u v hdisj
  obtain ⟨H, hHplanar, hHadj⟩ :=
    WilliamsonShmoys.planarDrawingOn_glue_bridge__p2m_bde12a09_c3ff_49b5_827a_2421e10fc278_a1
      A B S u v hAplanar hBplanar hAs hBs huS hvS
  refine ⟨H, ?_, hHplanar, ?_⟩
  · intro a b hab
    rcases (hsplit a b).mp hab with habA | habB
    · exact (hHadj a b).2 (Or.inl habA)
    · exact (hHadj a b).2 (Or.inr (Or.inl habB))
  · intro a b
    constructor
    · intro hab
      rcases (hHadj a b).1 hab with habA | habRest
      · exact Or.inl ((hsplit a b).2 (Or.inl habA))
      · rcases habRest with habB | hbridge
        · exact Or.inl ((hsplit a b).2 (Or.inr habB))
        · exact Or.inr hbridge
    · intro hab
      rcases hab with habG | hbridge
      · rcases (hsplit a b).1 habG with habA | habB
        · exact (hHadj a b).2 (Or.inl habA)
        · exact (hHadj a b).2 (Or.inr (Or.inl habB))
      · exact (hHadj a b).2 (Or.inr (Or.inr hbridge))
