-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_8bebbcb3_63fa_47e0_bd08_43c40080b6a9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:04:39.598528+00:00
-- url     : https://prove2.me/submissions/c1bf512b-7eb7-43bd-a1b6-19798825718e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_extension__p2m_6c2fd8cd_5f03_4713_95f5_290dacd849f4_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hNK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_edge_count_extension__p2m_6c2fd8cd_5f03_4713_95f5_290dacd849f4_a1
      N hN hV
  have hKN : K = N := hmax K hNK hK
  simpa [hKN] using hcount