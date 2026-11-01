-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_8b27cfb4_0f8b_46ed_98a5_9ae477e5a402_a1__p2m_8b27cfb4_0f8b_46ed_98a5_9ae477e5a402_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:29:31.479203+00:00
-- url     : https://prove2.me/submissions/cd4f3212-d4ff-4fa0-bacc-f0f90a95cecd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_c0d4ecaf_266f_445a_8f51_dc327adf9453_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation__p2m_c0d4ecaf_266f_445a_8f51_dc327adf9453_a1

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper :=
    WilliamsonShmoys.planar_edge_upper_bound__p2m_c0d4ecaf_266f_445a_8f51_dc327adf9453_a1
      K hcard hK
  by_contra hne
  have hnotge :
      ¬ 3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
    intro hlarge
    exact hne (Nat.le_antisymm hupper hlarge)
  have hsparse :
      K.edgeSet.ncard < 3 * Fintype.card V - 6 := Nat.lt_of_not_ge hnotge
  obtain ⟨L, hKL, hneq, hL⟩ :=
    WilliamsonShmoys.planar_edge_augmentation__p2m_c0d4ecaf_266f_445a_8f51_dc327adf9453_a1
      K hcard hK hsparse
  exact hneq (hmax L hKL hL)