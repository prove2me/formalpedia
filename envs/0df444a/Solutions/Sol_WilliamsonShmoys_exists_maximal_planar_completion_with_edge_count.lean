-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_completion_with_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:55:16.186591+00:00
-- url     : https://prove2.me/submissions/6d5db537-b203-4945-a06d-cd3aca658bb5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_edge_completion_v3
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_v3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hV : 3 <= Fintype.card V) :
    Exists (fun Y : SimpleGraph V =>
      And (LE.le X Y)
        (And (WilliamsonShmoys.HasPlanarDrawingOn Y)
          (Y.edgeSet.ncard = 3 * Fintype.card V - 6))) := by
  obtain ⟨Y, hXY, hY, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_edge_completion_v3 X hX
  have hcount :=
    WilliamsonShmoys.maximal_drawable_graph_edge_count_v3 Y hY hmax hV
  exact Exists.intro Y (And.intro hXY (And.intro hY hcount))