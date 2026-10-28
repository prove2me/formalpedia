-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_edge_count_lower_20f2cea7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:59:40.0271+00:00
-- url     : https://prove2.me/submissions/f168ba73-9c60-4a41-bd72-710fb13cbd70
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_lower_20f2cea7
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_20f2cea7

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hLdraw, hLbound⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_count_lower_20f2cea7 K hKdraw hCard
  have hLK : L ≤ K := hmax L hKL hLdraw
  have hmono := WilliamsonShmoys.edgeSet_ncard_mono_20f2cea7 L K hLK
  omega