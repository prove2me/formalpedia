-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_maximal_extension_euler
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:38:41.523882+00:00
-- url     : https://prove2.me/submissions/ead41f39-5da6-4282-904c-118c4bcc219e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_edge_count_of_inclusion_maximality

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 <= Fintype.card V) :
    ∃ R : SimpleGraph V,
      (∀ {u v}, Q.Adj u v → R.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      R.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨R, hQR, hR, hmax⟩ :=
    WilliamsonShmoys.planar_drawable_maximal_extension Q hdraw
  exact ⟨R, hQR, hR,
    WilliamsonShmoys.planar_drawable_maximal_edge_count_of_inclusion_maximality
      R hR hV hmax⟩