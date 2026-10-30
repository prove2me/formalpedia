-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_face_counts__p2m_d4ee878b_f197_42bb_afe9_c773b884d027_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:34:04.572266+00:00
-- url     : https://prove2.me/submissions/5bc3150a-9e5b-4bc6-8bb0-83f23cfac5f0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_5172cebe_7d77_4b25_aa7c_10802cca0895_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeFinset.card + 2 ∧
      2 * H.edgeFinset.card = 3 * f := by
  have hE :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_5172cebe_7d77_4b25_aa7c_10802cca0895_a1
      H hH hmax hcard
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega
