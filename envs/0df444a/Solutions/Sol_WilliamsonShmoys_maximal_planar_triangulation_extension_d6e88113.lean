-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangulation_extension_d6e88113
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:31:22.225008+00:00
-- url     : https://prove2.me/submissions/80114880-375b-4b1c-8d5f-1fe1886ec38e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_extension_d6e88113
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_d6e88113

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H) (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, HasPlanarDrawingOn K ∧
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hKdraw, hHK, hKconn, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_extension_d6e88113 H hdraw hconn hV
  exact ⟨K, hKdraw, hHK,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_d6e88113
      K hKdraw hKconn hV hmax⟩