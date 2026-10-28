-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_supergraph_with_euler_edge_count_a4f892c9_f19c_464f_8d5c_153cf02f5773
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:41:40.604816+00:00
-- url     : https://prove2.me/submissions/52ec2a9c-a828-4ba0-ac1d-26a30312de0f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_for_euler_count
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_euler_face_equations_for_euler_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_for_euler_count K hK
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_drawable_euler_face_equations_for_euler_count L hL hMax hCard
  refine ⟨L, hKL, hL, ?_⟩
  omega