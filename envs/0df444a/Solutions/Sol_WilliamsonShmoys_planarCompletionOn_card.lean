-- Prove2me | solution 1 for WilliamsonShmoys.planarCompletionOn_card
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:48:26.517171+00:00
-- url     : https://prove2.me/submissions/832d3503-c775-4f02-a53a-bdb762ce911a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_maximal_2d69255633d74159
import Theorems.Thm_WilliamsonShmoys_maximal_planar_card_2d69255633d74159

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ P : SimpleGraph V, G.edgeSet ⊆ P.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      P.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨P, hGP, hP, hmax⟩ :=
    WilliamsonShmoys.planar_completion_maximal_2d69255633d74159 G hG
  refine ⟨P, hGP, hP, ?_⟩
  exact WilliamsonShmoys.maximal_planar_card_2d69255633d74159 P hV hP hmax