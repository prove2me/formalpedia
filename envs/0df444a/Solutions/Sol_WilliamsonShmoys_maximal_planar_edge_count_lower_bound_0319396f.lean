-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_0319396f
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:23:34.864447+00:00
-- url     : https://prove2.me/submissions/21dc5a39-84c2-433f-b959-0416e2d846c3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_triangulated_planar_extension_0319396f

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by
  obtain ⟨K, hHK, hK, hKcard⟩ :=
    WilliamsonShmoys.triangulated_planar_extension_0319396f H hH hV
  have hKH : K = H := hmax K hHK hK
  have hbound : 3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := hKcard.ge
  simpa [hKH] using hbound