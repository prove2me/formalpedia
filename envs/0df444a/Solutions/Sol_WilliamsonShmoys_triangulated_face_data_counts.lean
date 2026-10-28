-- Prove2me | solution 1 for WilliamsonShmoys.triangulated_face_data_counts
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:18:55.281971+00:00
-- url     : https://prove2.me/submissions/375feb26-8868-4bfe-b2ae-1bab972cde2d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangulatedPlanarFaceData

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {H : SimpleGraph V}
    (D : WilliamsonShmoys.TriangulatedPlanarFaceData H) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f = 2 * H.edgeSet.ncard := by
  classical
  letI := D.fintypeFaces
  letI := D.fintypeEdges
  refine ⟨Fintype.card D.Faces, ?_, ?_⟩
  · have := D.euler; rw [D.edge_count] at this; exact this
  · rw [← D.edge_count]
    have h1 : ∀ f, (Finset.univ.bipartiteAbove D.incident f).card = 3 := by
      intro f; rw [← D.face_triangle f]
      unfold Finset.bipartiteAbove
      convert (Fintype.card_subtype (fun e => D.incident f e)).symm
    have h2 : ∀ e, (Finset.univ.bipartiteBelow D.incident e).card = 2 := by
      intro e; rw [← D.edge_two_sides e]
      unfold Finset.bipartiteBelow
      convert (Fintype.card_subtype (fun f => D.incident f e)).symm
    have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (Finset.univ : Finset D.Faces)) (t := (Finset.univ : Finset D.Edges)) (r := D.incident)
    simp only [h1, h2, Finset.sum_const, Finset.card_univ, smul_eq_mul] at key
    linarith
