-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_euler_face_data__p2m_1fae8d59_e553_43b6_adc4_9f2b440ae2bb_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:19:23.875445+00:00
-- url     : https://prove2.me/submissions/8b946e36-381c-4422-a39a-708ae28203b1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_has_triangulation_edge_count__p2m_7f938502_4ebe_49de_af5d_b80801e1f743_a5

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K' : SimpleGraph V, H ≤ K' → WilliamsonShmoys.HasPlanarDrawingOn K' → K' = H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    ∃ F : ℕ,
      Fintype.card V + F = H.edgeFinset.card + 2 ∧
      2 * H.edgeFinset.card = 3 * F := by
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  obtain ⟨K, hHK, hKplanar, hKcard⟩ :=
    WilliamsonShmoys.planar_drawingOn_has_triangulation_edge_count__p2m_7f938502_4ebe_49de_af5d_b80801e1f743_a5 H hH hcard
  have hKH : K = H := hmax K hHK hKplanar
  subst K
  have hE : H.edgeFinset.card + 6 = 3 * Fintype.card V := by
    simpa using hKcard
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega