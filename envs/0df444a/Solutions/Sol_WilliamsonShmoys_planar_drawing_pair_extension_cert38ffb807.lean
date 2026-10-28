-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_pair_extension_cert38ffb807
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:56:12.896507+00:00
-- url     : https://prove2.me/submissions/995ac4e2-c4c5-48f3-8d7d-8895f3771956
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_adjoin_cross_component_edge

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V) (huv : u ≠ v)
    (hnot : ¬ Relation.ReflTransGen G.Adj u v) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      Relation.ReflTransGen H.Adj u v := by
  obtain ⟨H, hGH, hHdraw, huvH⟩ :=
    WilliamsonShmoys.planar_drawing_adjoin_cross_component_edge
      G hdraw u v huv hnot
  exact ⟨H, hGH, hHdraw, Relation.ReflTransGen.single huvH⟩