-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_maximal_extension__p2m_46fe5fa5_fbe5_4667_8617_73807c0b1344_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:19:30.846696+00:00
-- url     : https://prove2.me/submissions/56c787cd-6bfa-4d30-88be-88c47662c972

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_of_finite_graph_predicate__p2m_7793594c_aadb_4407_9b10_d0dd43a77b6e_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_mono__p2m_7793594c_aadb_4407_9b10_d0dd43a77b6e_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) := by
  classical
  let hereditary : ∀ ⦃G K : SimpleGraph V⦄, G ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → WilliamsonShmoys.HasPlanarDrawingOn G := by
    intro G K hGK hK
    exact WilliamsonShmoys.planar_drawing_mono__p2m_7793594c_aadb_4407_9b10_d0dd43a77b6e_a1 hGK hK
  exact WilliamsonShmoys.exists_maximal_extension_of_finite_graph_predicate__p2m_7793594c_aadb_4407_9b10_d0dd43a77b6e_a1
    WilliamsonShmoys.HasPlanarDrawingOn H hplanar hereditary