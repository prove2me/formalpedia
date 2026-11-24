-- Prove2me | solution 3 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_710ae9cd_06e1_4ca5_a820_3c02fa6bdb35_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:30:19.248735+00:00
-- url     : https://prove2.me/submissions/29544401-a5a8-4668-ab02-e7e7e787c8c8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  classical
  have hV' : 3 ≤ Fintype.card V := by
    first
    | exact hcard
    | (rw [Set.ncard_univ, Nat.card_eq_fintype_card] at hcard; exact hcard)
  have hub : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc H hV' hH
  obtain ⟨H0, hGH0, hH0, hle0, hc0⟩ := WilliamsonShmoys.planar_drawing_extension_for_edge_bound_ef555edc H hV' hH
  have hMax0 : ∀ J : SimpleGraph V, H0 ≤ J → HasPlanarDrawingOn J → J ≤ H0 := by
    intro J hHJ hJ
    have hJb := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc J hV' hJ
    have heq := Set.eq_of_subset_of_ncard_le (SimpleGraph.edgeSet_subset_edgeSet.mpr hHJ) (by omega) (Set.toFinite _)
    exact (SimpleGraph.edgeSet_inj.mp heq.symm).le
  have hC0 : H0.Connected := WilliamsonShmoys.maximal_planar_drawingOn_connected H0 hH0 hMax0 hV'
  have hs0 : H.edgeSet ⊆ H0.edgeSet := SimpleGraph.edgeSet_subset_edgeSet.mpr hGH0
  have ha0 : ∀ ⦃u v : V⦄, H.Adj u v → H0.Adj u v := fun u v h => hGH0 h
  have ha0' : ∀ u v : V, H.Adj u v → H0.Adj u v := fun u v h => hGH0 h
  have hes0 : ∀ e, e ∈ H.edgeSet → e ∈ H0.edgeSet := fun e he => hs0 he
  have hR0 : ∀ u v : V, Relation.ReflTransGen H0.Adj u v := fun u v => (SimpleGraph.reachable_iff_reflTransGen _ _).mp (hC0.preconnected u v)
  have hRe0 : ∀ u v : V, H0.Reachable u v := fun u v => hC0.preconnected u v
  have hW0 : ∀ u v : V, Nonempty (H0.Walk u v) := fun u v => hC0.preconnected u v
  have hz0 : (H.edgeSet.ncard : ℤ) ≤ (H0.edgeSet.ncard : ℤ) := by exact_mod_cast hle0
  have hcm0 : 3 * Fintype.card V = H0.edgeSet.ncard + 6 := hc0.symm
  have hcl0 : 3 * Fintype.card V ≤ H0.edgeSet.ncard + 6 := by omega
  have hcs0 : H0.edgeSet.ncard = 3 * Fintype.card V - 6 := by omega
  have hct0 : H0.edgeSet.ncard = 3 * (Fintype.card V - 2) := by omega
  have hct1 : 3 * (Fintype.card V - 2) ≤ H0.edgeSet.ncard := by omega
  first
  | (simp only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, Set.ncard_univ, Nat.card_eq_fintype_card] at *; omega)
  | omega
  | assumption
  | exact hconnX
  | (intro u v; exact (SimpleGraph.reachable_iff_reflTransGen _ _).mp (hconnX.preconnected u v))
  | (refine ⟨H0, ?_⟩; and_intros <;> first | assumption | omega | exact_mod_cast hle0 | (simp only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, Set.ncard_univ, Nat.card_eq_fintype_card] at *; omega) | exact Ne.symm ‹_› | (intro h; exact hnle0 h))
  | (refine ⟨H0, Classical.decRel _, ?_⟩; and_intros <;> first | assumption | omega | exact_mod_cast hle0 | (simp only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, Set.ncard_univ, Nat.card_eq_fintype_card] at *; omega) | exact Ne.symm ‹_› | (intro h; exact hnle0 h))
  | (refine ⟨H0, ?_⟩; first | assumption | omega | exact_mod_cast hle0 | (simp only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, Set.ncard_univ, Nat.card_eq_fintype_card] at *; omega) | exact Ne.symm ‹_› | (intro h; exact hnle0 h))
