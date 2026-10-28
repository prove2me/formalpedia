-- Prove2me | solution 1 for WilliamsonShmoys.drawing_euler_face_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:55:41.487089+00:00
-- url     : https://prove2.me/submissions/7a0e8205-0a63-4809-a35a-a1439f21b4d6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula_7c5eea9e
import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound_7c5eea9e

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∃ F : ℕ,
      Fintype.card V + F = K.edgeSet.ncard + 2 ∧
      3 * F <= 2 * K.edgeSet.ncard := by
  obtain ⟨F, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_formula_7c5eea9e K hconn hdraw
  have hEdge := WilliamsonShmoys.simple_planar_edge_bound_7c5eea9e K hdraw hV
  refine ⟨F, hEuler, ?_⟩
  omega