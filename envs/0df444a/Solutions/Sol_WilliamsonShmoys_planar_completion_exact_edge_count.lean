-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_exact_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:19:09.106151+00:00
-- url     : https://prove2.me/submissions/8818bd2c-c948-4dcb-a3ab-39977d52c37e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_maximal_extension_exists_bcd4e9c3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_bcd4e9c3
import Theorems.Thm_WilliamsonShmoys_sparse_extension_strict_bcd4e9c3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hsparse : H.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 ∧
      ¬ K.edgeSet ⊆ H.edgeSet := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_completion_maximal_extension_exists_bcd4e9c3 H hH
  have hcard := WilliamsonShmoys.maximal_planar_edge_count_bcd4e9c3 K hV hK hmax
  have hstrict := WilliamsonShmoys.sparse_extension_strict_bcd4e9c3
    H K hV hHK hcard hsparse
  exact ⟨K, hHK, hK, hcard, hstrict⟩