-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_augmentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:12:11.988983+00:00
-- url     : https://prove2.me/submissions/a66e16c2-f402-4996-952a-ed46fbdf9e48
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_strict_supergraph
import Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_maximal_connected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  have hStep : ∀ K : SimpleGraph V, G ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → ¬ K.Connected →
      ∃ L : SimpleGraph V, K < L ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by
    intro K hGK hK hKDisconnected
    exact WilliamsonShmoys.planar_disconnected_has_strict_supergraph K hK hKDisconnected
  exact WilliamsonShmoys.finite_planar_supergraph_maximal_connected G hG hStep