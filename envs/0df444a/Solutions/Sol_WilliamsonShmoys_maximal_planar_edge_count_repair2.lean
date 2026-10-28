-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_repair2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:58:44.992245+00:00
-- url     : https://prove2.me/submissions/44da724c-62fc-4d0c-b862-fc5a4e48ee2d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph_same_vertices

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hmax : ∀ T : SimpleGraph V, S ≤ T →
      WilliamsonShmoys.HasPlanarDrawingOn T → T = S) :
    S.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hST, hT, hcount⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_supergraph_same_vertices
      S hV hS
  have hTS : T = S := hmax T hST hT
  rw [hTS] at hcount
  exact hcount