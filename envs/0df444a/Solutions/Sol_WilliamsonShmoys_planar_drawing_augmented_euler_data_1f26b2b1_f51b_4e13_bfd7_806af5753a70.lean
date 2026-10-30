-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_augmented_euler_data_1f26b2b1_f51b_4e13_bfd7_806af5753a70
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:54:40.794249+00:00
-- url     : https://prove2.me/submissions/1abaea00-e746-48d0-be90-8a611b753b74

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_augmentation
import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ M f : ℕ, K.edgeSet.ncard ≤ M ∧ Fintype.card V + f = M + 2 ∧ 3 * f ≤ 2 * M := by
  obtain ⟨H, hH, hEdges, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_edge_maximal_augmentation K hV hK
  refine ⟨H.edgeSet.ncard, 2 * Fintype.card V - 4, hEdges, ?_, ?_⟩
  · omega
  · omega