-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:18:10.109742+00:00
-- url     : https://prove2.me/submissions/661e1e1b-79c4-40fd-b935-0ddbbf7dac7e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L.edgeSet ⊂ M.edgeSet → ¬ HasPlanarDrawingOn M)
    (hLK : L ≤ K)
    (hKDraw : HasPlanarDrawingOn K) :
    L = K := by
  by_contra hne
  have hlt : L < K := lt_of_le_of_ne hLK hne
  exact hMax K (SimpleGraph.edgeSet_ssubset_edgeSet.mpr hlt) hKDraw
