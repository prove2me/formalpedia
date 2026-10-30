-- Prove2me | solution 1 for WilliamsonShmoys.drawable_completion_triangulation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:52:48.201371+00:00
-- url     : https://prove2.me/submissions/35803ccc-92fb-434d-97f2-e5d1b8ff1fb3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_completion_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_of_planar_drawing

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 <= Fintype.card V) :
    exists P : SimpleGraph V,
      (forall {u v}, N.Adj u v -> P.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn P /\
      P.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  let hExtension :=
    WilliamsonShmoys.drawable_completion_maximal_extension N hdraw
  let P := Classical.choose hExtension
  have hSpec := Classical.choose_spec hExtension
  have hNP : forall {u v}, N.Adj u v -> P.Adj u v := hSpec.1
  have hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P := hSpec.2.1
  have hPmax :=
    hSpec.2.2
  have hcount :=
    WilliamsonShmoys.maximal_drawable_graph_edge_count_of_planar_drawing
      P hPdraw hPmax hV
  exact Exists.intro P (And.intro hNP (And.intro hPdraw hcount))