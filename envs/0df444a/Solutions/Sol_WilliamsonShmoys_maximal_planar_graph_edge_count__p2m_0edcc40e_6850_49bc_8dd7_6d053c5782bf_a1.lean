-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_0edcc40e_6850_49bc_8dd7_6d053c5782bf_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:22:44.351859+00:00
-- url     : https://prove2.me/submissions/b68e51f0-06b5-422f-8726-9d5f602b2307
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_face_count_certificate__p2m_dd6d4a28_ff1c_4910_81ae_1b1a3100063c_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hCard : 3 <= Fintype.card V)
    (hT : HasPlanarDrawingOn T)
    (hMax : ∀ u v, u ≠ v → ¬ T.Adj u v →
      ¬ ∃ U : SimpleGraph V,
        (∀ x y, T.Adj x y → U.Adj x y) ∧
        HasPlanarDrawingOn U ∧ U.Adj u v) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨f, hEuler, hTriangles⟩ :=
    WilliamsonShmoys.maximal_planar_graph_face_count_certificate__p2m_dd6d4a28_ff1c_4910_81ae_1b1a3100063c_a1
      T hCard hT hMax
  omega