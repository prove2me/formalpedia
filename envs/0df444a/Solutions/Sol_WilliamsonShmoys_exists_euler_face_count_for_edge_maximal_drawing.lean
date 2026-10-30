-- Prove2me | solution 1 for WilliamsonShmoys.exists_euler_face_count_for_edge_maximal_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:28:42.271119+00:00
-- url     : https://prove2.me/submissions/d7ebca76-9dbf-4b0f-ac10-89e73cc47ea0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_n_ge_three

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 ∧ 3 * f = 2 * L.edgeSet.ncard := by
  have hE : L.edgeSet.ncard = 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.maximal_planar_edge_count_for_n_ge_three L hL hMax hCard
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> rw [hE] <;> omega