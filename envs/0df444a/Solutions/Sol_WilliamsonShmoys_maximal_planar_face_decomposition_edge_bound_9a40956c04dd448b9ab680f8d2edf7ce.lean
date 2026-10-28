-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition_edge_bound_9a40956c04dd448b9ab680f8d2edf7ce
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:36:46.474004+00:00
-- url     : https://prove2.me/submissions/827cb939-08d0-4102-a033-3884362b297d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_edge_count_for_maximal_face_decomposition_2218dce211984abc9cb0bb5b50a2d3f4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → H = K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by
  obtain ⟨H, hKH, hHdraw, hHcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion_edge_count_for_maximal_face_decomposition_2218dce211984abc9cb0bb5b50a2d3f4
      K hK hCard
  have hHK : H = K := hmax H hKH hHdraw
  subst H
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega