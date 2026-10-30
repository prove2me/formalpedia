-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_536aaf66_0a7c_4c8d_b8d1_73a7e039d5bd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T07:09:12.396407+00:00
-- url     : https://prove2.me/submissions/bf13e2bb-cfc1-40c0-a731-c0a3e59072d8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc


set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  classical
  have hB := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc G hCard hDraw
  obtain ⟨Tz, hlez, hTz, hcz⟩ := WilliamsonShmoys.planar_graph_has_triangulated_supergraph G hCard hDraw
  first
  | omega
  | exact ⟨Tz, hlez, hTz, by omega⟩
  | exact ⟨Tz, fun u v hh => hlez hh, hTz, by omega⟩
  | exact ⟨Tz, fun {u v} hh => hlez hh, hTz, by omega⟩
  | exact ⟨Tz, SimpleGraph.edgeSet_mono hlez, hTz, by omega⟩
  | exact ⟨Tz, hlez, hTz, by omega⟩
  | exact ⟨Tz, hlez, hTz, by omega, by omega⟩
  | exact ⟨Tz, hlez, hTz, by omega⟩
  | exact ⟨Tz, hlez, hTz, le_of_eq hcz.symm⟩
  | exact ⟨2 * Fintype.card V - 4, by omega, by omega⟩
  | exact ⟨3 * Fintype.card V - 6, 2 * Fintype.card V - 4, by omega, by omega, by omega⟩
