-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_edge_lower_bound__p2m_6582e0a3_76e8_4a07_8065_8715ca29a41a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:51:17.75399+00:00
-- url     : https://prove2.me/submissions/b06bfc56-7d28-4b59-9131-06dd82ec4f8d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulating_supergraph__p2m_a2bdd39c_3a82_41f8_ad95_4704547f58a7_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     3 * Fintype.card V ≤ N.edgeFinset.card + 6) := by
  classical
  obtain ⟨P, hNP, hP, hEq⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulating_supergraph__p2m_a2bdd39c_3a82_41f8_ad95_4704547f58a7_a1
      N hN hcard
  have hPN : P = N := hmax P hNP hP
  subst P
  exact le_of_eq hEq