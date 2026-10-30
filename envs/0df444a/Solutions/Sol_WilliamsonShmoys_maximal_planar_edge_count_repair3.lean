-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_repair3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:55:13.360227+00:00
-- url     : https://prove2.me/submissions/4210be69-ce8c-4d77-b226-f90a5ecdb8eb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_extension_repair3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
      (∀ u v, H.Adj u v → K.Adj u v) →
      ∀ u v, K.Adj u v → H.Adj u v)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hK, hHK, hcount⟩ :=
    WilliamsonShmoys.exists_triangulated_planar_extension_repair3 H hH hCard
  have hEq : K = H := by
    ext u v
    constructor
    · exact hmax K hK (by
        intro x y hxy
        exact hHK x y hxy) u v
    · exact hHK u v
  simpa [hEq] using hcount