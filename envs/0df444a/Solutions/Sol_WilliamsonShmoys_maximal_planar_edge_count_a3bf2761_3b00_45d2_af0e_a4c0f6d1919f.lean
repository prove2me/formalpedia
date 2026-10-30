-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_a3bf2761_3b00_45d2_af0e_a4c0f6d1919f
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:17:05.355982+00:00
-- url     : https://prove2.me/submissions/abcc0a1b-5cd4-4454-a5cc-20826c1ec018

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count_fcb16b3d

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    (L.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨M, hLM, hMdraw, hMcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_edge_count_fcb16b3d
      L hL hCard
  have hEq : M = L := hMax M hLM hMdraw
  simpa [hEq] using hMcount