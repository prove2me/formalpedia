-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_maximal_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:28:03.573999+00:00
-- url     : https://prove2.me/submissions/42d76b61-5ed5-4b98-a992-0f966bc674f4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangulation_extension

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨L, hKL, hdrawL, hcard⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_triangulation_extension K hV hdraw hconn
  have hLK : L = K := hmax L hKL hdrawL
  subst L
  exact le_of_eq hcard.symm