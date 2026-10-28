-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_edge_count_fe39cb94_f82e_4553_8662_9097c26d5d3d
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:40:39.883001+00:00
-- url     : https://prove2.me/submissions/9d6b6939-8d00-4b15-b54a-948be79b1ae0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_edge_maximal_extension_fab67c4d
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_fab67c4d

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨L, hKL, hL, hLMax⟩ :=
    WilliamsonShmoys.drawable_edge_maximal_extension_fab67c4d K hK
  have hEdgeSet : K.edgeSet = L.edgeSet := by
    apply Set.Subset.antisymm hKL
    intro e he
    by_contra hnot
    have hne : K.edgeSet ≠ L.edgeSet := by
      intro h
      have hmem : e ∈ K.edgeSet := by
        rw [h]
        exact he
      exact hnot hmem
    exact hMax L (Set.ssubset_iff_subset_ne.mpr ⟨hKL, hne⟩) hL
  have hCount :=
    WilliamsonShmoys.edge_count_of_maximal_planar_drawing_fab67c4d L hL hCard hLMax
  have hNcard : K.edgeSet.ncard = L.edgeSet.ncard :=
    congrArg Set.ncard hEdgeSet
  rw [hNcard, hCount]