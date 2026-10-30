-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_density
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:09:48.765416+00:00
-- url     : https://prove2.me/submissions/e444303f-f8bd-4b5e-9436-b04d6763e7a8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_density

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, HasPlanarDrawingOn L ∧
      (∀ u v, K.Adj u v → L.Adj u v) ∧
      3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨L, hL, hKL, hmax⟩ :=
    WilliamsonShmoys.planar_completion_maximal_extension K hK hCard
  refine ⟨L, hL, hKL, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_density L hL hCard hmax