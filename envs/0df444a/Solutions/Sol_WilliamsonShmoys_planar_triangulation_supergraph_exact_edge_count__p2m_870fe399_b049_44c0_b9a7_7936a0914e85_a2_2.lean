-- Prove2me | solution 2 for WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_870fe399_b049_44c0_b9a7_7936a0914e85_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T10:10:39.476263+00:00
-- url     : https://prove2.me/submissions/0fcd0ded-8b4d-42da-bfda-39556a6c8726

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_augmentation__p2m_be074bdb_79a8_40c0_b245_62762170066e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_count__p2m_8c5f7fcd_4410_4b31_b397_bfdf744b7888_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        (letI : DecidableRel K.Adj := dK;
          3 * Fintype.card V - 6 = K.edgeFinset.card) := by
  classical
  obtain ⟨K, hJK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_augmentation__p2m_be074bdb_79a8_40c0_b245_62762170066e_a1
      J hJ hcard
  let dK : DecidableRel K.Adj := Classical.decRel K.Adj
  have hmaxEq : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
    intro L hKL hL
    exact le_antisymm (hmax L hKL hL) hKL
  have heuler :=
    WilliamsonShmoys.maximal_planar_euler_count__p2m_8c5f7fcd_4410_4b31_b397_bfdf744b7888_a2
      K hK hmaxEq hcard
  refine ⟨K, dK, hJK, hK, ?_⟩
  change 3 * Fintype.card V - 6 = K.edgeFinset.card
  omega
