-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_870fe399_b049_44c0_b9a7_7936a0914e85_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:32:08.163469+00:00
-- url     : https://prove2.me/submissions/d33ceb5a-5322-4d75-b574-5fc083b355a1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_augmentation__p2m_be074bdb_79a8_40c0_b245_62762170066e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_exact_edge_count__p2m_be074bdb_79a8_40c0_b245_62762170066e_a1

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
  refine ⟨K, dK, hJK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_be074bdb_79a8_40c0_b245_62762170066e_a1
    K dK hK hmax