-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_6301d38c_0224_4362_a676_de729a46b58e_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:45:00.765197+00:00
-- url     : https://prove2.me/submissions/72e25099-0235-4df1-81ef-ea864b2403ac

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_389ae2e7_9395_452b_8575_19bfbaf74b9e_a2
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_389ae2e7_9395_452b_8575_19bfbaf74b9e_a2
      K hK hCard
  have hLK : L ≤ K := hMax L hKL hL
  have hEq : L = K := le_antisymm hLK hKL
  simpa [hEq] using hCount