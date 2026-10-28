-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulation_extension_for_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:56:55.707836+00:00
-- url     : https://prove2.me/submissions/da5fd206-4caf-4d1e-9e37-d2af3faf6400
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_IsMaximalPlanarOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_on_card_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H) :
    exists K : SimpleGraph V,
      H <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_extension H hHplanar
  have hcount := WilliamsonShmoys.maximal_planar_on_card_edge_count K hKmax hV
  exact ⟨K, hHK, hKmax.1, hcount⟩