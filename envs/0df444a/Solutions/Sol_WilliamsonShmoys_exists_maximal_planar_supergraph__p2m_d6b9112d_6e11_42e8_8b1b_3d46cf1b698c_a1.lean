-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_d6b9112d_6e11_42e8_8b1b_3d46cf1b698c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:56:51.643874+00:00
-- url     : https://prove2.me/submissions/f96650a4-1218-4410-936a-ea07cff186df

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_predicate_has_maximal_element__p2m_c0ec6b8f_fcbf_4b2c_8dba_71231ff2f6b6_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by
  classical
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  let P : SimpleGraph V → Prop := fun H => G ≤ H ∧ HasPlanarDrawingOn H
  have hP : ∃ H, P H := ⟨G, le_rfl, hG⟩
  obtain ⟨K, hK, hmax⟩ :=
    WilliamsonShmoys.finite_predicate_has_maximal_element__p2m_c0ec6b8f_fcbf_4b2c_8dba_71231ff2f6b6_a1
      P hP
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hL
  exact hmax L ⟨hK.1.trans hKL, hL⟩ hKL