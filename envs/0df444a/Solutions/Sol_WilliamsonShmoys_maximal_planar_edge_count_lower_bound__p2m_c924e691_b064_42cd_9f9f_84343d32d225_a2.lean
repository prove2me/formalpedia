-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c924e691_b064_42cd_9f9f_84343d32d225_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:32:22.308982+00:00
-- url     : https://prove2.me/submissions/667796ce-5915-47d4-9927-7c039a451057

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_exact_edge_count__p2m_adc88660_2f73_451b_8969_754986caab7a_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ M : SimpleGraph V,
      N.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet = N.edgeSet) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by
  obtain ⟨M, hNM, hM, hcard⟩ :=
    WilliamsonShmoys.planar_extension_exact_edge_count__p2m_adc88660_2f73_451b_8969_754986caab7a_a1
      N hV hN
  have hEq := hmax M hNM hM
  rw [← hEq]
  exact le_of_eq hcard.symm