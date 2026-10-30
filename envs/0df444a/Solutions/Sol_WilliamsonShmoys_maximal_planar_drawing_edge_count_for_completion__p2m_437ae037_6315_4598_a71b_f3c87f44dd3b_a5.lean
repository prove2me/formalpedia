-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_for_completion__p2m_437ae037_6315_4598_a71b_f3c87f44dd3b_a5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T02:21:24.682866+00:00
-- url     : https://prove2.me/submissions/73061695-fc8b-4a1b-8f39-a2f91cde6148

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_exact_edge_count_completion__p2m_536aaf66_0a7c_4c8d_b8d1_73a7e039d5bd_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K →
      H.edgeSet ⊂ K.edgeSet → False)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hsub, hKdraw, hKcount⟩ :=
    WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_536aaf66_0a7c_4c8d_b8d1_73a7e039d5bd_a2
      H hHdraw hCard
  have hnot : ¬ H.edgeSet ⊂ K.edgeSet := by
    intro hs
    exact hMax K hKdraw hs
  have heq : H.edgeSet = K.edgeSet := by
    apply Set.Subset.antisymm hsub
    intro e he
    by_contra hne
    apply hnot
    exact ⟨hsub, fun hKH => hne (hKH he)⟩
  rw [heq]
  exact hKcount