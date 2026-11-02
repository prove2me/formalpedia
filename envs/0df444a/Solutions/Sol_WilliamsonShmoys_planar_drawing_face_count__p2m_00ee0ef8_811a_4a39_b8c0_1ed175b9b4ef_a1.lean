-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_count__p2m_00ee0ef8_811a_4a39_b8c0_1ed175b9b4ef_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:40:50.036964+00:00
-- url     : https://prove2.me/submissions/89732556-7b34-4dbe-a118-d3c07ac90382
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_characteristic__p2m_b664cddc_4710_40ab_ab7d_a96b7cb12f1c_a2
import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound__p2m_b664cddc_4710_40ab_ab7d_a96b7cb12f1c_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hV : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeFinset.card + 2 ∧
      3 * f ≤ 2 * K.edgeFinset.card := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_characteristic__p2m_b664cddc_4710_40ab_ab7d_a96b7cb12f1c_a2
      K hconn hK
  refine ⟨f, hEuler, ?_⟩
  have hDensity :=
    WilliamsonShmoys.simple_planar_edge_bound__p2m_b664cddc_4710_40ab_ab7d_a96b7cb12f1c_a2
      K hV hconn hK
  omega