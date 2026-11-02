-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_344124b5_d420_40df_b6d0_816baecb63ba_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:59:45.597222+00:00
-- url     : https://prove2.me/submissions/998c6101-8921-49be-815a-75e74bf2f17d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_c9a4a27a_018e_4f14_8723_166da166188f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_euler_equations__p2m_c9a4a27a_018e_4f14_8723_166da166188f_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
    fun K => Classical.decRel K.Adj
  obtain ⟨M, hHM, hCardLe, hM, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_c9a4a27a_018e_4f14_8723_166da166188f_a1
      H hH hcard
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_euler_equations__p2m_c9a4a27a_018e_4f14_8723_166da166188f_a1
      M hM hcard hMax
  have hMbound : M.edgeFinset.card + 6 = 3 * Fintype.card V := by omega
  exact le_trans hCardLe (by omega)