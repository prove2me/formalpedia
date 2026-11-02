-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_exact_edge_extension__p2m_2d3bff7d_8a6a_45d8_b748_fea14c5aa101_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:01:48.875538+00:00
-- url     : https://prove2.me/submissions/7a92c453-04fb-4b0e-977b-7e52856ca79e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_extension__p2m_8f423dbe_14e3_49a1_828e_7cd49c2ddeb4_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_three_n_minus_six_edges__p2m_8f423dbe_14e3_49a1_828e_7cd49c2ddeb4_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : WilliamsonShmoys.HasPlanarDrawingOn H) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 = K.edgeFinset.card := by
  classical
  letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
  obtain ⟨ K, hHK, hdrawK, hmaxK ⟩ :=
    WilliamsonShmoys.planar_drawing_has_edge_maximal_extension__p2m_8f423dbe_14e3_49a1_828e_7cd49c2ddeb4_a1 H hcard hdrawing
  refine ⟨ K, hHK, hdrawK, ?_ ⟩
  exact WilliamsonShmoys.maximal_planar_drawing_has_three_n_minus_six_edges__p2m_8f423dbe_14e3_49a1_828e_7cd49c2ddeb4_a1 K hcard hdrawK hmaxK