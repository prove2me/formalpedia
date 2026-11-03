-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_757b64a4_4ecc_451f_8c8e_f98c58cc600e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:46:52.719294+00:00
-- url     : https://prove2.me/submissions/93a123c6-7afc-44c4-b678-5d759a8fcdb6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation_below_triangulation_bound__p2m_a09da42e_0803_4d50_ab6c_6ed525cd351e_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      3 * Fintype.card V ≤ L.edgeFinset.card + 6) := by
  classical
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  by_contra h
  have hsparse : L.edgeFinset.card + 6 < 3 * Fintype.card V := by omega
  obtain ⟨M, hLM, hne, hdraw⟩ :=
    WilliamsonShmoys.planar_drawing_edge_augmentation_below_triangulation_bound__p2m_a09da42e_0803_4d50_ab6c_6ed525cd351e_a1
      L hV hL hsparse
  exact hne (hMax M hLM hdraw)