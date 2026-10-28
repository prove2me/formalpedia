-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_finite_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:22:57.82044+00:00
-- url     : https://prove2.me/submissions/5a050497-c66e-430c-960c-1c5910873b29

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_finite

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.Connected ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  obtain ⟨K, hHK, hK, hcount, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_finite H hH
  exact ⟨K, hHK, hK, hconn.mono hHK, hcount, hmax⟩