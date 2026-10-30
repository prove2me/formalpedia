-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_maximal_edge_count_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:11:48.240289+00:00
-- url     : https://prove2.me/submissions/6fe0c35f-3bce-48ac-89ac-cf559c048893

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_edge_count_20261026

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ K : SimpleGraph V, L ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = L)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  obtain ⟨K, hLK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion_edge_count_20261026
      L hL hV
  have hKL : K = L := hmax K hLK hK
  simpa [hKL] using hcount.symm
