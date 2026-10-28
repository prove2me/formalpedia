-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_e4624ca0
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:05:52.648776+00:00
-- url     : https://prove2.me/submissions/14c8ce1a-fe91-4279-a659-8eda1f86fccd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_v4
import Theorems.Thm_WilliamsonShmoys_drawable_graph_can_add_edge_below_maximum_v4

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, HasPlanarDrawingOn M → L ≤ M → M = L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :
      (L.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 :=
    WilliamsonShmoys.planar_edge_count_upper_bound_v4 L hdraw hV
  have hNotBelow :
      ¬ ((L.edgeSet.ncard : Int) <
          3 * (Fintype.card V : Int) - 6) := by
    intro hBelow
    obtain ⟨M, hStrict, hMdraw⟩ :=
      WilliamsonShmoys.drawable_graph_can_add_edge_below_maximum_v4
        L hdraw hV hBelow
    have hLE : L ≤ M := le_of_lt hStrict
    have hEq : M = L := hmax M hMdraw hLE
    exact (ne_of_lt hStrict) hEq.symm
  have hEqInt :
      (L.edgeSet.ncard : Int) + 6 =
        3 * (Fintype.card V : Int) := by
    omega
  omega