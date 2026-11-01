-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_drawing_face_count__p2m_8d49dd8d_df70_44ed_9374_0df305c3481e_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:43:23.377204+00:00
-- url     : https://prove2.me/submissions/2d90214d-b915-4992-bd69-ba0a6e314b78
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion__p2m_3649950b_31dd_4927_b1e8_a61f090b394f_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U ≤ T)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel T.Adj := Classical.decRel T.Adj
    ∃ f : ℕ,
      Fintype.card V + f = T.edgeFinset.card + 2 ∧
      3 * f = 2 * T.edgeFinset.card := by
  classical
  letI : DecidableRel T.Adj := Classical.decRel T.Adj
  obtain ⟨U, hTU, hU, hUc⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_3649950b_31dd_4927_b1e8_a61f090b394f_a1
      T hT hcard
  letI : DecidableRel U.Adj := Classical.decRel U.Adj
  have hUT : U ≤ T := hmax U hTU hU
  have hEq : T = U := le_antisymm hTU hUT
  cases hEq
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega