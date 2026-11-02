-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_18bbe9c1_8b0d_4062_b19f_3ec33678fcd4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:45:23.776337+00:00
-- url     : https://prove2.me/submissions/23cdc8ef-b952-472d-987f-c4e9b278a861
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_extension__p2m_2d3bff7d_8a6a_45d8_b748_fea14c5aa101_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
    3 * Fintype.card V - 6 ≤ H.edgeFinset.card := by
  letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
  obtain ⟨K, hHK, hdrawK, hedges⟩ :=
    WilliamsonShmoys.planar_drawing_has_exact_edge_extension__p2m_2d3bff7d_8a6a_45d8_b748_fea14c5aa101_a1
      H hcard hdrawing
  have hKH : K = H := hmax K hHK hdrawK
  rw [hKH] at hedges
  exact hedges.le