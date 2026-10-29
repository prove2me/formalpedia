-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_20261027
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:57:54.584853+00:00
-- url     : https://prove2.me/submissions/f5bf0e81-3842-4aaa-b8da-03b59e9eb29f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_completion_edge_count

set_option autoImplicit false

/-- The exact target follows by applying the finite planar augmentation theorem
on the same vertex set, then maximality identifies the augmentation with `H`. -/
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hHmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKplanar, hKcount⟩ :=
    WilliamsonShmoys.exists_planar_completion_edge_count H hV hHplanar
  have hKH : K = H := hHmax K hHK hKplanar
  simpa [hKH] using hKcount