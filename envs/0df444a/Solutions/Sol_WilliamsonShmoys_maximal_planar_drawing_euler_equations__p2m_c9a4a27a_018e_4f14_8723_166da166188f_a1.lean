-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_euler_equations__p2m_c9a4a27a_018e_4f14_8723_166da166188f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:13:38.254878+00:00
-- url     : https://prove2.me/submissions/ab016699-3938-4679-9652-3da594095f99
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_of_maximal_planar__p2m_ab3c4834_8b15_4a63_8fca_25572aaa5eac_a2
import Theorems.Thm_WilliamsonShmoys_planar_euler_formula__p2m_ab3c4834_8b15_4a63_8fca_25572aaa5eac_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_incidence__p2m_ab3c4834_8b15_4a63_8fca_25572aaa5eac_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ f : ℕ,
      Fintype.card V + f = M.edgeFinset.card + 2 ∧
      3 * f = 2 * M.edgeFinset.card := by
  classical
  letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
    fun K => Classical.decRel K.Adj
  have hconn :=
    WilliamsonShmoys.connected_of_maximal_planar__p2m_ab3c4834_8b15_4a63_8fca_25572aaa5eac_a2
      M hM hcard hMax
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_euler_formula__p2m_ab3c4834_8b15_4a63_8fca_25572aaa5eac_a2
      M hM hconn
  refine ⟨f, hEuler, ?_⟩
  exact
    WilliamsonShmoys.maximal_planar_face_incidence__p2m_ab3c4834_8b15_4a63_8fca_25572aaa5eac_a2
      M hM hcard hMax f hEuler