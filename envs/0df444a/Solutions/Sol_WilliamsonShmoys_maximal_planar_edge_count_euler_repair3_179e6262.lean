-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_euler_repair3_179e6262
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:53:27.721614+00:00
-- url     : https://prove2.me/submissions/f096e700-beb0-4b53-ad4b-735054b1f58b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_and_incidence

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hMax : ∀ K : SimpleGraph V, J ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = J)
    (hCard : 3 ≤ Fintype.card V) :
    J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_euler_and_incidence
      J hJ hMax hCard
  omega