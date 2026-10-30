-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:33:25.448618+00:00
-- url     : https://prove2.me/submissions/ebd77686-e41c-4b94-9ae0-383e3492fd5f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_completion_cardinality

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hmax : ∀ W : SimpleGraph V, Z ≤ W →
      WilliamsonShmoys.HasPlanarDrawingOn W → W ≤ Z) :
    3 * Fintype.card V ≤ Z.edgeSet.ncard + 6 := by
  obtain ⟨W, hZW, hW, hcard⟩ :=
    WilliamsonShmoys.maximal_drawable_graph_completion_cardinality Z hV hZ
  have hWZ : W ≤ Z := hmax W hZW hW
  have hEq : W = Z := le_antisymm hWZ hZW
  have hcardZ : Z.edgeSet.ncard + 6 = 3 * Fintype.card V := by
    simpa [hEq] using hcard
  exact le_of_eq hcardZ.symm