-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:42:48.633279+00:00
-- url     : https://prove2.me/submissions/7b8c275a-f704-4cce-a488-6680d41d3cc9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula_for_certificate
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_for_certificate

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ f : Nat,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * K.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_formula_for_certificate K hdraw hconn
  have hEdge :=
    WilliamsonShmoys.planar_simple_edge_bound_for_certificate K hV hdraw
  exact ⟨f, hEuler, by omega⟩