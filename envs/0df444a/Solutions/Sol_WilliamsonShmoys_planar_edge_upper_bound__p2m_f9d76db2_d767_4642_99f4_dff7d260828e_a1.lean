-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_f9d76db2_d767_4642_99f4_dff7d260828e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:37:27.999756+00:00
-- url     : https://prove2.me/submissions/c6cdd566-2bcf-4543-ba66-55fe77376cca

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulating_supergraph__p2m_f289c5f6_bcae_4951_8202_39fcc0f6c95e_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V) :
    M.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨N, hsub, hdraw, hcard_le, hN⟩ :=
    WilliamsonShmoys.planar_triangulating_supergraph__p2m_f289c5f6_bcae_4951_8202_39fcc0f6c95e_a1
      M hplanar hcard
  omega