-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation__p2m_c0d4ecaf_266f_445a_8f51_dc327adf9453_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:39:38.077975+00:00
-- url     : https://prove2.me/submissions/90bce21a-b3be-4f2a-be81-ce372879aca1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_maximal_extension__p2m_fc48bf70_67b7_4d76_9c36_25eeec7debc5_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_maximal_edge_bound__p2m_fc48bf70_67b7_4d76_9c36_25eeec7debc5_a1

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hsparse : K.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ L ≠ K ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_edge_augmentation_maximal_extension__p2m_fc48bf70_67b7_4d76_9c36_25eeec7debc5_a1
      K hK
  have hbound : 3 * Fintype.card V - 6 ≤ L.edgeSet.ncard :=
    WilliamsonShmoys.planar_edge_augmentation_maximal_edge_bound__p2m_fc48bf70_67b7_4d76_9c36_25eeec7debc5_a1
      L hcard hL hmax
  refine ⟨L, hKL, ?_, hL⟩
  intro hEq
  subst L
  exact (not_lt_of_ge hbound) hsparse