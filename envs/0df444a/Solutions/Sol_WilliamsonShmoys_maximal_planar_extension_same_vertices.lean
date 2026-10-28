-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_extension_same_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:07:21.386029+00:00
-- url     : https://prove2.me/submissions/2d69100b-41d2-44fa-932e-127346875ce1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_cd050b01_9a07_4b9b_9132_918bb6a60ec5
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_cd050b01_9a07_4b9b_9132_918bb6a60ec5

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hRconn : R.Connected)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ H : SimpleGraph V,
      R ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) ∧
      R.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hRH, hHplanar, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_cd050b01_9a07_4b9b_9132_918bb6a60ec5 R hR
  exact ⟨H, hRH, hHplanar, hmax,
    WilliamsonShmoys.edgeSet_ncard_mono_cd050b01_9a07_4b9b_9132_918bb6a60ec5 R H hRH⟩