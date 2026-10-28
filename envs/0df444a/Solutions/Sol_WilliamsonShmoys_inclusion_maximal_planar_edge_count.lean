-- Prove2me | solution 1 for WilliamsonShmoys.inclusion_maximal_planar_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:49:17.027906+00:00
-- url     : https://prove2.me/submissions/46b69dbe-2f74-4bb2-806f-27d9b52f70f4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_with_maximal_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      Set.Subset H.edgeSet K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      Set.Subset K.edgeSet H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKplanar, hKcount⟩ :=
    WilliamsonShmoys.planar_extension_with_maximal_edge_count H hV hH
  have hKH : Set.Subset K.edgeSet H.edgeSet := hMax K hHK hKplanar
  have hEq : H.edgeSet = K.edgeSet := Set.Subset.antisymm hHK hKH
  rw [hEq]
  exact hKcount