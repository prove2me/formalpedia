-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_620608d3_0799_426b_beeb_eff4e8e41716_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:57:19.937809+00:00
-- url     : https://prove2.me/submissions/8cf8b279-264e-4ad1-afa9-803d63e0a3a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_368c0d6c_27a0_4bf2_9016_cc54673fe776_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, HasPlanarDrawingOn L →
      (∀ u v, K.Adj u v → L.Adj u v) → L = K)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hL, hsub, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_368c0d6c_27a0_4bf2_9016_cc54673fe776_a1
      K hK hcard
  have hLK : L = K := hmax L hL hsub
  rw [hLK] at hcount
  exact le_of_eq hcount