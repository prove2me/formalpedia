-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_a3e0b5a8_b607_4050_8296_f0effeafa525_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:37:55.246756+00:00
-- url     : https://prove2.me/submissions/aba8dd6a-f4be-4355-948c-ba0d2f2b9f09
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_23bdb811_aa64_4006_9931_e87966df2d08_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_23bdb811_aa64_4006_9931_e87966df2d08_a1
      K hK hV
  have hLK : L = K := hmax L hKL hL
  rw [hLK] at hcount
  omega