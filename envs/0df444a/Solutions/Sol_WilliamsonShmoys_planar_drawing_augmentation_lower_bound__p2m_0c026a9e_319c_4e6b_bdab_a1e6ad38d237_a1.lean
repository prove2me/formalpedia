-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_augmentation_lower_bound__p2m_0c026a9e_319c_4e6b_bdab_a1e6ad38d237_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:43:27.288571+00:00
-- url     : https://prove2.me/submissions/74f5de1d-7a95-4eb1-a362-7517985d19b9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_maximal_extension__p2m_0835c3dc_b66c_4223_9284_2bc5bd7f2cf4_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_maximal_edge_bound__p2m_0835c3dc_b66c_4223_9284_2bc5bd7f2cf4_a2
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
       3 * Fintype.card V - 6 <= L.edgeFinset.card) := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_augmentation_maximal_extension__p2m_0835c3dc_b66c_4223_9284_2bc5bd7f2cf4_a2
      K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.planar_drawing_augmentation_maximal_edge_bound__p2m_0835c3dc_b66c_4223_9284_2bc5bd7f2cf4_a2
      L hV hL hmax⟩