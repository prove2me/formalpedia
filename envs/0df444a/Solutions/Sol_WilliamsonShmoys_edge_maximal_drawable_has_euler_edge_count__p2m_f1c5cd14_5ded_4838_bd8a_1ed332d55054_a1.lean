-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_drawable_has_euler_edge_count__p2m_f1c5cd14_5ded_4838_bd8a_1ed332d55054_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:45:02.961218+00:00
-- url     : https://prove2.me/submissions/08421007-a5d0-45e6-a72f-743f4934ffd7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_extension__p2m_b4c9393f_ee8c_44c0_9df7_8513af7ec896_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hMax : ∀ (K : SimpleGraph V) [DecidableRel K.Adj],
      H.edgeFinset ⊆ K.edgeFinset → HasPlanarDrawingOn K →
        K.edgeFinset ⊆ H.edgeFinset)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨K, hKdec, hHK, hKdraw, hKcard⟩ :=
    WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_b4c9393f_ee8c_44c0_9df7_8513af7ec896_a1
      H hH hV
  letI : DecidableRel K.Adj := hKdec
  have hKH : K.edgeFinset ⊆ H.edgeFinset := hMax K hHK hKdraw
  have heq : H.edgeFinset = K.edgeFinset := Finset.Subset.antisymm hHK hKH
  rw [heq, hKcard]