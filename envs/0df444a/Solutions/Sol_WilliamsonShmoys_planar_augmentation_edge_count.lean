-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:05:24.817144+00:00
-- url     : https://prove2.me/submissions/a886646d-3a8f-4c95-b346-14e294845526

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_on_vertices
import Theorems.Thm_WilliamsonShmoys_exists_euler_face_count_for_edge_maximal_drawing

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph_on_vertices K hK
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.exists_euler_face_count_for_edge_maximal_drawing L hL hMax hCard
  refine ⟨L, hKL, hL, ?_⟩
  omega