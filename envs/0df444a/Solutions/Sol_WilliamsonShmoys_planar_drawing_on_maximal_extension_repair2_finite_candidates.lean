-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_on_maximal_extension_repair2_finite_candidates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:42:35.072862+00:00
-- url     : https://prove2.me/submissions/8bc4369b-a43b-41fb-ba92-44a1c3acff8a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    Set.Finite {M : SimpleGraph V | G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M} :=
  Set.toFinite _
