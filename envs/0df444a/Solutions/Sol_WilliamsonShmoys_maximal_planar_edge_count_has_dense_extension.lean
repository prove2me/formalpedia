-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_has_dense_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:47:45.935193+00:00
-- url     : https://prove2.me/submissions/d5cfc63f-6713-4d24-a2e0-564877c26b3e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_exists
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_cardinality_lower_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension_exists H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_edge_cardinality_lower_bound K hK hmax hV⟩