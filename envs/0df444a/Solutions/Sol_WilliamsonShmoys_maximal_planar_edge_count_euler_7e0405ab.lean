-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_euler_7e0405ab
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:40:02.867693+00:00
-- url     : https://prove2.me/submissions/b1a88f09-3d12-4dab-82bc-8e307d448e4d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_euler_extension

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ J : SimpleGraph V, H ≤ J →
      WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨J, hHJ, hJplanar, hcount⟩ :=
    WilliamsonShmoys.maximal_planar_edge_count_euler_extension H hH hCard
  have hJH : J ≤ H := hmax J hHJ hJplanar
  have hEq : J = H := le_antisymm hJH hHJ
  simpa [hEq] using hcount