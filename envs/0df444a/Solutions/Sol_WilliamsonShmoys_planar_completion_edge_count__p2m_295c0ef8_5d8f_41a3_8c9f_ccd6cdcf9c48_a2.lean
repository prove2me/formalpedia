-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_edge_count__p2m_295c0ef8_5d8f_41a3_8c9f_ccd6cdcf9c48_a2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T07:11:07.185462+00:00
-- url     : https://prove2.me/submissions/e2a811de-2004-468b-b51a-865d36626ea1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc



theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  classical
  have hB := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc N hCard hN
  obtain ⟨Tz, hlez, hTz, hcz⟩ := WilliamsonShmoys.planar_graph_has_triangulated_supergraph N hCard hN
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
