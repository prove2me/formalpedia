-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_drawable_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:22:56.030574+00:00
-- url     : https://prove2.me/submissions/527c09f9-0637-47f5-8771-302ba9c984b7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ T : SimpleGraph V,
      (∀ {u v}, S.Adj u v → T.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn T → T = S) :
    S.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hST, hTdraw, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_edge_count S hdraw hV
  have hTS : T = S := hmax T hST hTdraw
  simpa [hTS] using hcount