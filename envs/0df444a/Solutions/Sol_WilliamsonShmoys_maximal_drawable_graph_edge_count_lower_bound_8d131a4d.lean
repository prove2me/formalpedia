-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_8d131a4d
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:41:11.865159+00:00
-- url     : https://prove2.me/submissions/8554c2a3-f2d1-48a0-b9eb-3ef69b1fb31f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_edge_count_lower_bound

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn N)
    (hV : 3 <= Fintype.card V)
    (hmax : forall P : SimpleGraph V, N <= P -> HasPlanarDrawingOn P -> P <= N) :
    3 * (Fintype.card V : Int) - 6 <= (N.edgeSet.ncard : Int) := by
  obtain ⟨P, hNP, hdrawP, hbound⟩ :=
    WilliamsonShmoys.drawable_supergraph_edge_count_lower_bound N hdraw hV
  have hPN : P <= N := hmax P hNP hdrawP
  have hEq : N = P := le_antisymm hNP hPN
  calc
    3 * (Fintype.card V : Int) - 6 <= (P.edgeSet.ncard : Int) := hbound
    _ = (N.edgeSet.ncard : Int) :=
      congrArg (fun G : SimpleGraph V => (G.edgeSet.ncard : Int)) hEq.symm