-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_lower_bound__p2m_99986598_6392_4501_ac0d_a0cd3c835fd3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:30:18.0982+00:00
-- url     : https://prove2.me/submissions/d0e450cb-17a7-49e8-b9de-32f860d71052

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_5e34af62_bc93_4e27_8f77_f0a9265acaf1_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5e34af62_bc93_4e27_8f77_f0a9265acaf1_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V, L ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨K, hLK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_5e34af62_bc93_4e27_8f77_f0a9265acaf1_a1
      L hL
  have hcount := WilliamsonShmoys.maximal_planar_edge_count__p2m_5e34af62_bc93_4e27_8f77_f0a9265acaf1_a1
    K hcard hK hmax
  exact ⟨K, hLK, hK, Nat.le_of_eq hcount.symm⟩
