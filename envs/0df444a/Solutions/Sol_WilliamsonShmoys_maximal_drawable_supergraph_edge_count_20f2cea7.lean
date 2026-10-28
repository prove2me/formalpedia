-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_edge_count_20f2cea7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:29:39.943999+00:00
-- url     : https://prove2.me/submissions/b9ef3f4f-c6d5-4bad-82e0-e15c88ef874b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_augmentation_below_triangulation_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  by_contra hnot
  have hsmall : 3 * Fintype.card V > L.edgeSet.ncard + 6 := by omega
  obtain ⟨M, hLM, hMdraw, hML⟩ :=
    WilliamsonShmoys.planar_graph_augmentation_below_triangulation_bound
      L hLdraw hCard hsmall
  have hEq : M = L := hmax M hLM hMdraw
  exact hML hEq