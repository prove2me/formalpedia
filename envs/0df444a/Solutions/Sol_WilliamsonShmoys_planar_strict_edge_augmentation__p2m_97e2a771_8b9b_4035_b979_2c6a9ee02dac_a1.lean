-- Prove2me | solution 1 for WilliamsonShmoys.planar_strict_edge_augmentation__p2m_97e2a771_8b9b_4035_b979_2c6a9ee02dac_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:20:37.223871+00:00
-- url     : https://prove2.me/submissions/2c7cc94b-6891-4acc-a790-d727e0246a9a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_671e5c30_1b1f_403c_8a8b_f487cd0d141b_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_671e5c30_1b1f_403c_8a8b_f487cd0d141b_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hSparse : M.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ H : SimpleGraph V, M ≤ H ∧ H ≠ M ∧ HasPlanarDrawingOn H := by
  obtain ⟨H, hsub, hH, hmax⟩ := WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_671e5c30_1b1f_403c_8a8b_f487cd0d141b_a1 M hM
  refine ⟨H, hsub, ?_, hH⟩
  intro hEq
  have hCount := WilliamsonShmoys.maximal_drawable_edge_count__p2m_671e5c30_1b1f_403c_8a8b_f487cd0d141b_a1 H hH hmax hCard
  rw [hEq] at hCount
  omega