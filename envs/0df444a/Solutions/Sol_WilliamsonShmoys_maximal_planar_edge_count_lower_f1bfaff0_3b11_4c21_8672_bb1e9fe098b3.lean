-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_f1bfaff0_3b11_4c21_8672_bb1e9fe098b3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:51:39.20807+00:00
-- url     : https://prove2.me/submissions/72ef3142-7442-46e6-8326-ae9e985f2dee

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_density

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, HasPlanarDrawingOn L →
      (∀ u v, K.Adj u v → L.Adj u v) →
      ∀ u v, L.Adj u v → K.Adj u v)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hL, hKL, hDense⟩ :=
    WilliamsonShmoys.planar_completion_density K hK hCard
  have hLK : ∀ u v, L.Adj u v → K.Adj u v := hMax L hL hKL
  have hEq : K = L := by
    ext u v
    exact ⟨hKL u v, hLK u v⟩
  simpa [hEq] using hDense