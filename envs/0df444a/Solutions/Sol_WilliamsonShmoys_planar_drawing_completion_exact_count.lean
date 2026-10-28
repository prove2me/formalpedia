-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion_exact_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:55:08.92008+00:00
-- url     : https://prove2.me/submissions/9ce37125-45ed-4184-a246-7020df8a79b2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_efb0a43e_finite_maximal_drawable_supergraph
import Theorems.Thm_WilliamsonShmoys_efb0a43e_maximal_drawable_exact_edge_count

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hNK, hK, hmax⟩ :=
    WilliamsonShmoys.efb0a43e_finite_maximal_drawable_supergraph N hN
  exact ⟨K, hNK, hK,
    WilliamsonShmoys.efb0a43e_maximal_drawable_exact_edge_count K hK hCard hmax⟩