-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:09:42.40131+00:00
-- url     : https://prove2.me/submissions/e3654403-4d50-449a-9512-f7ac598d5c88
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count_for_maximal_edge_lower_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet ⊆ N.edgeSet) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by
  obtain ⟨K, hNK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_completion_edge_count_for_maximal_edge_lower_bound N hV hN
  have hKN : K.edgeSet ⊆ N.edgeSet := hmax K hNK hK
  have hsets : K.edgeSet = N.edgeSet := Set.Subset.antisymm hKN hNK
  rw [← hsets]
  omega
