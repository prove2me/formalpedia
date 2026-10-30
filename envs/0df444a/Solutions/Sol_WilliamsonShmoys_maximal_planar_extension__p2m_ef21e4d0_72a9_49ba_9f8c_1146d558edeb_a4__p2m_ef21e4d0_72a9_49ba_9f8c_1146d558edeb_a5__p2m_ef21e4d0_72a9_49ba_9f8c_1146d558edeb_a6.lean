-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_ef21e4d0_72a9_49ba_9f8c_1146d558edeb_a4__p2m_ef21e4d0_72a9_49ba_9f8c_1146d558edeb_a5__p2m_ef21e4d0_72a9_49ba_9f8c_1146d558edeb_a6
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T07:09:23.615473+00:00
-- url     : https://prove2.me/submissions/18db1a85-4e6a-440b-9608-233d8656521d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hCard : 3 <= Fintype.card V)
    (hT : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      (∀ x y, T.Adj x y → U.Adj x y) ∧
      HasPlanarDrawingOn U ∧
      U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  classical
  have hB := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc T hCard hT
  obtain ⟨Tz, hlez, hTz, hcz⟩ := WilliamsonShmoys.planar_graph_has_triangulated_supergraph T hCard hT
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
