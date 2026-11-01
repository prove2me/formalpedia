-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_maximal_extension__p2m_fc48bf70_67b7_4d76_9c36_25eeec7debc5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:43:46.784813+00:00
-- url     : https://prove2.me/submissions/3a846ac8-18f9-46bf-8d93-59ed9a97145b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_type__p2m_1299aa4d_98c0_4add_b63d_d780039a027b_a1
import Theorems.Thm_WilliamsonShmoys_finite_property_maximal_extension__p2m_1299aa4d_98c0_4add_b63d_d780039a027b_a1

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M →
          WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  letI : Finite (SimpleGraph V) :=
    WilliamsonShmoys.finite_simpleGraph_type__p2m_1299aa4d_98c0_4add_b63d_d780039a027b_a1
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  exact WilliamsonShmoys.finite_property_maximal_extension__p2m_1299aa4d_98c0_4add_b63d_d780039a027b_a1
    (P := WilliamsonShmoys.HasPlanarDrawingOn) K hK