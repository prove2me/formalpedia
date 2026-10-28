-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_augmentation_repair2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:22:14.254848+00:00
-- url     : https://prove2.me/submissions/908ae2e4-c2f2-4d55-9dcf-ca543133e485
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_edge_count__p2m_772ef201_63b7_4b42_b9f5_1f5abd1bb02f_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (hE : N.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ M : SimpleGraph V, N < M ∧ WilliamsonShmoys.HasPlanarDrawingOn M := by
  obtain ⟨M, hNM, hM, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_edge_count__p2m_772ef201_63b7_4b42_b9f5_1f5abd1bb02f_a2 N hN hV
  have hne : N ≠ M := by
    intro h
    subst M
    omega
  exact ⟨M, lt_of_le_of_ne hNM hne, hM⟩