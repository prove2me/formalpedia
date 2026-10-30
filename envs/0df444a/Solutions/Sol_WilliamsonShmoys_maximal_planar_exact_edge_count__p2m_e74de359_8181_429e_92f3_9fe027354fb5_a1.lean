-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_e74de359_8181_429e_92f3_9fe027354fb5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:21:16.71881+00:00
-- url     : https://prove2.me/submissions/aaed670e-b39f-47aa-b3a6-4a97f2dd785a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_d657b208_a585_46f8_ac13_1623c7b09177_a2
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_augmentation__p2m_d657b208_a585_46f8_ac13_1623c7b09177_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L -> L = K) :
    letI : DecidableRel K.Adj := Classical.decRel _
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hLower⟩ :=
    WilliamsonShmoys.planar_triangulation_augmentation__p2m_d657b208_a585_46f8_ac13_1623c7b09177_a2
      K hK hcard
  have hLK : L = K := hmax L hKL hL
  subst L
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_d657b208_a585_46f8_ac13_1623c7b09177_a2
      K hK hcard
  · exact hLower