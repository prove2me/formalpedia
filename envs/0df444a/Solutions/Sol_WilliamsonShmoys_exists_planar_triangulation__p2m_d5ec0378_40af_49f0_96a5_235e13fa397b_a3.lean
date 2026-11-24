-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation__p2m_d5ec0378_40af_49f0_96a5_235e13fa397b_a3
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:03:34.501094+00:00
-- url     : https://prove2.me/submissions/5df67505-dfdd-4df0-b899-fc91f4a45a8d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ u v, Relation.ReflTransGen H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hbot : HasPlanarDrawingOn (⊥ : SimpleGraph V) := by
    obtain ⟨e⟩ : Nonempty (V ↪ ℝ) := ⟨⟨fun v => ((Fintype.equivFin V v : ℕ) : ℝ), fun a b h => by
      have := Nat.cast_injective h
      exact (Fintype.equivFin V).injective (Fin.ext this)⟩⟩
    refine ⟨fun v => (e v, 0), fun _ _ _ => 0, ?_, ?_, ?_⟩
    · intro a b h; exact e.injective (congrArg Prod.fst h)
    · intro u v _ h; exact absurd h (by simp)
    · intro u v x y _ _ h; exact absurd h (by simp)
  obtain ⟨H0, -, hH0, -, h⟩ := WilliamsonShmoys.planar_drawing_extension_for_edge_bound_ef555edc (⊥ : SimpleGraph V) hV hbot
  have hMax0 : ∀ J : SimpleGraph V, H0 ≤ J → HasPlanarDrawingOn J → J ≤ H0 := by
    intro J hHJ hJ
    have hJb := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc J hV hJ
    have hsub := SimpleGraph.edgeSet_subset_edgeSet.mpr hHJ
    have heq := Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
    exact (SimpleGraph.edgeSet_inj.mp heq.symm).le
  have hC0 := WilliamsonShmoys.maximal_planar_drawingOn_connected H0 hH0 hMax0 hV
  exact ⟨H0, fun u v => (SimpleGraph.reachable_iff_reflTransGen _ _).mp (hC0.preconnected u v), hH0, h⟩
