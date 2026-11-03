-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_adb36ea0_1077_447f_b2c5_a4177e2cdb6e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:03:34.102885+00:00
-- url     : https://prove2.me/submissions/87cd542e-03b3-4dbc-bcee-f1632b4fbcc2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_a0f5e8a0_e0da_456d_9ce8_2c77e5e78796_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, HasPlanarDrawingOn L →
      (∀ u v, K.Adj u v → L.Adj u v) →
      (∀ u v, L.Adj u v → K.Adj u v)) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    3 * Fintype.card V = K.edgeFinset.card + 6 := by
  classical
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  obtain ⟨L, hL, hKL, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_a0f5e8a0_e0da_456d_9ce8_2c77e5e78796_a1
      K hV hK
  have hLK : ∀ u v, L.Adj u v → K.Adj u v := hmax L hL hKL
  have hEq : L = K := by
    ext u v
    exact ⟨hLK u v, hKL u v⟩
  rw [hEq] at hcount
  exact hcount