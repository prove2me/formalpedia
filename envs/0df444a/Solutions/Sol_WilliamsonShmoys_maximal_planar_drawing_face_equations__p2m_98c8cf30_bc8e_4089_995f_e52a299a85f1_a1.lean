-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_face_equations__p2m_98c8cf30_bc8e_4089_995f_e52a299a85f1_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:41:55.68988+00:00
-- url     : https://prove2.me/submissions/05d1652b-21a2-4647-871d-660da83a3f3e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangulation_extension__p2m_8a77ef9e_b782_4199_be1b_94d3ad7b0b10_a4
import Theorems.Thm_WilliamsonShmoys_face_equations_of_edge_count__p2m_8a77ef9e_b782_4199_be1b_94d3ad7b0b10_a4
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → L = M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  obtain ⟨M, hLM, hM, hCount⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_triangulation_extension__p2m_8a77ef9e_b782_4199_be1b_94d3ad7b0b10_a4
      L hL hCard
  have hEq : L = M := hMax M hLM hM
  have hEdge : L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
    simpa [hEq] using hCount
  exact WilliamsonShmoys.face_equations_of_edge_count__p2m_8a77ef9e_b782_4199_be1b_94d3ad7b0b10_a4
    (Fintype.card V) L.edgeSet.ncard hCard hEdge