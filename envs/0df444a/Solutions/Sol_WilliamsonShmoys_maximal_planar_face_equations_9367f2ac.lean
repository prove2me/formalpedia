-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_equations_9367f2ac
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:18:18.793383+00:00
-- url     : https://prove2.me/submissions/93ce37bd-a518-4186-9837-3da0b2a79955

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_43062042_0cdc_4c51_9c62_1a9950b577b3_a1
import Theorems.Thm_WilliamsonShmoys_face_equations_of_edge_count__p2m_43062042_0cdc_4c51_9c62_1a9950b577b3_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  have hEdges :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_43062042_0cdc_4c51_9c62_1a9950b577b3_a1
      L hDraw hMax hCard
  exact WilliamsonShmoys.face_equations_of_edge_count__p2m_43062042_0cdc_4c51_9c62_1a9950b577b3_a1
    (Fintype.card V) L.edgeSet.ncard hCard hEdges