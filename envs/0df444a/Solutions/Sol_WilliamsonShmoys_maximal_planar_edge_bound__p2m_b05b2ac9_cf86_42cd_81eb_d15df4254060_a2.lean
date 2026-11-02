-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:40:42.844909+00:00
-- url     : https://prove2.me/submissions/30011f35-ec55-4a39-b3ea-b18d5e8e4fed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_d59a8e60_bd9e_4339_9c63_4718b5d88d29_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hMaximal : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_d59a8e60_bd9e_4339_9c63_4718b5d88d29_a1
      K hV hK
  have hLK : L = K := hMaximal L hKL hL
  rw [hLK] at hcount
  exact hcount.le