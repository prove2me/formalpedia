-- Prove2me | solution 2 for WilliamsonShmoys.planar_partition_extension__p2m_6eb1d1e9_05be_4cdb_8344_dedf44e2bf5b_a3
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:03:36.89674+00:00
-- url     : https://prove2.me/submissions/fec03566-9970-43c1-aca8-be75f5e1d5e5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (A : Set V)
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (hcross : ∀ ⦃u v : V⦄, u ∈ A → v ∈ Aᶜ → ¬ M.Adj u v)
    (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧ ¬ N ≤ M := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hAc
  have hab : ¬ M.Reachable a b := by
    rintro ⟨w⟩
    have key : ∀ (x y : V) (w : M.Walk x y), x ∈ A → y ∈ A := by
      intro x y w
      induction w with
      | nil => exact id
      | @cons x y z hadj w ih =>
        intro hx
        apply ih
        by_contra hy
        exact hcross hx hy hadj
    exact hb (key a b w ha)
  obtain ⟨N, hMN, hN⟩ := WilliamsonShmoys.planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1 M hM a b hab
  exact ⟨N, hMN.le, hN, fun h => hMN.ne (le_antisymm hMN.le h)⟩
