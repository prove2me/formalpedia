-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extends_to_triangulation__p2m_6ce17d90_7e34_4ced_9818_f205b3115d6a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T07:10:10.820158+00:00
-- url     : https://prove2.me/submissions/f936ecb3-6620-444e-be79-18741e0fb0a9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hP : HasPlanarDrawingOn P) : ∃ Q : SimpleGraph V, P ≤ Q ∧ HasPlanarDrawingOn Q ∧ Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  classical
  have hB := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc P hV hP
  obtain ⟨Tz, hlez, hTz, hcz⟩ := WilliamsonShmoys.planar_graph_has_triangulated_supergraph P hV hP
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
