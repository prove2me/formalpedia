-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_face_bound__p2m_f80212f3_e77c_4cfe_8939_73f581dec5be_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:57:28.580205+00:00
-- url     : https://prove2.me/submissions/684d995b-3297-441d-b6a5-9a4b7987b9cb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_formula__p2m_0c722b40_f62a_4eb9_8c3e_41b6d8bfbb51_a1
import Theorems.Thm_WilliamsonShmoys_connected_simple_planar_edge_bound__p2m_0c722b40_f62a_4eb9_8c3e_41b6d8bfbb51_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : HasPlanarDrawingOn J)
    (hconn : ∀ u v : V, Nonempty (J.Walk u v))
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ f : ℕ,
      Fintype.card V + f = J.edgeFinset.card + 2 ∧
      3 * f ≤ 2 * J.edgeFinset.card := by
  classical
  letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
    fun K => Classical.decRel K.Adj
  obtain ⟨f, heuler⟩ := connected_planar_drawing_euler_formula__p2m_0c722b40_f62a_4eb9_8c3e_41b6d8bfbb51_a1 J hJ hconn
  have hedge := connected_simple_planar_edge_bound__p2m_0c722b40_f62a_4eb9_8c3e_41b6d8bfbb51_a1 J hJ hconn hcard
  exact ⟨f, heuler, by omega⟩