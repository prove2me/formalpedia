-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_target
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:41:08.41703+00:00
-- url     : https://prove2.me/submissions/4100d1ec-faec-46ea-ae4b-1767cc903d8c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_has_dense_extension

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hbound⟩ :=
    WilliamsonShmoys.maximal_planar_edge_count_has_dense_extension H hH hV
  have hEq : K = H := hMax K hHK hK
  simpa [hEq] using hbound