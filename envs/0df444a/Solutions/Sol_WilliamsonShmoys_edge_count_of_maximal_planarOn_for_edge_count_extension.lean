-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planarOn_for_edge_count_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:51:11.66861+00:00
-- url     : https://prove2.me/submissions/101e3d4a-cce2-4c02-95b0-f29b319e6974
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count_for_edge_count_extension

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : HasPlanarDrawingOn J ∧
      ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
        J.edgeSet ⊆ K.edgeSet → K.edgeSet ⊆ J.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hK, hJK, hKcount⟩ :=
    WilliamsonShmoys.planar_completion_edge_count_for_edge_count_extension
      J hJ.1 hV
  have hKJ : K.edgeSet ⊆ J.edgeSet := hJ.2 K hK hJK
  have hEq : K.edgeSet = J.edgeSet := Set.Subset.antisymm hKJ hJK
  simpa [hEq] using hKcount