-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_maximal_edge_count__p2m_d65752b0_c280_4c98_926b_0ae69c395723_a1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T07:08:35.37403+00:00
-- url     : https://prove2.me/submissions/22e75e01-2358-47ee-b42c-c6a8519aebd6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc


set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  classical
  have hB := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc G hCard hG
  obtain ⟨Tz, hlez, hTz, hcz⟩ := WilliamsonShmoys.planar_graph_has_triangulated_supergraph G hCard hG
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
