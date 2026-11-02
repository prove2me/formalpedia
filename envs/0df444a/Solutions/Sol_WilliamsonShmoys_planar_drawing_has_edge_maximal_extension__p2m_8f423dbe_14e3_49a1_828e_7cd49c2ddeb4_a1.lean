-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_edge_maximal_extension__p2m_8f423dbe_14e3_49a1_828e_7cd49c2ddeb4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:49:07.511149+00:00
-- url     : https://prove2.me/submissions/344623ca-47b3-4c8f-b1a2-9753959a1530

import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite__p2m_f4b47241_0114_4ac8_84bb_0550b2f73838_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : WilliamsonShmoys.HasPlanarDrawingOn H) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
  exact WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_f4b47241_0114_4ac8_84bb_0550b2f73838_a1
    H WilliamsonShmoys.HasPlanarDrawingOn hdrawing