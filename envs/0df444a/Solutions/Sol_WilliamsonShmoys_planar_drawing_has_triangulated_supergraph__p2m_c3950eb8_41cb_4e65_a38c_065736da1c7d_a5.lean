-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_supergraph__p2m_c3950eb8_41cb_4e65_a38c_065736da1c7d_a5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:01:04.44071+00:00
-- url     : https://prove2.me/submissions/a3837598-e40d-4b23-80a7-8ea6d65830f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_supergraph__p2m_32f2f9ec_d3c5_47a8_bbed_e2be5e927c82_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (hKdec : DecidableRel K.Adj) (f : Nat),
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧
      H.edgeFinset.card ≤ K.edgeFinset.card ∧
      K.edgeFinset.card + 2 = Fintype.card V + f ∧
      3 * f = 2 * K.edgeFinset.card := by
  classical
  obtain ⟨K, hKdec, hHK, hmono, he⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulated_supergraph__p2m_32f2f9ec_d3c5_47a8_bbed_e2be5e927c82_a3
      H hcard hH
  refine ⟨K, hKdec, 2 * Fintype.card V - 4, hHK, hmono, ?_, ?_⟩ <;> omega