-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_maximal_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:11:58.275866+00:00
-- url     : https://prove2.me/submissions/d6a059a0-87b0-4a17-92b5-eadb945df08c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_supergraph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hmax : forall T : SimpleGraph V,
      S <= T -> WilliamsonShmoys.HasPlanarDrawingOn T -> T <= S) :
    3 * Fintype.card V <= S.edgeSet.ncard + 6 := by
  obtain ⟨T, hST, hT, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulated_supergraph S hV hS
  have hTS : T <= S := hmax T hST hT
  have hEq : S = T := le_antisymm hST hTS
  simpa [hEq] using (le_of_eq hcount)