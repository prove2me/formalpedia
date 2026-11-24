-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_graph_has_triangulated_edge_count__p2m_7235810a_9787_44ff_bc97_6b6cda77c472_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:30:29.349201+00:00
-- url     : https://prove2.me/submissions/bf8f698c-1756-4de8-bb26-c44404f2c247

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
    (W : SimpleGraph V)
    (hW : HasPlanarDrawingOn W)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ X : SimpleGraph V, W ≤ X → HasPlanarDrawingOn X → X ≤ W) :
    letI : DecidableRel W.Adj := Classical.decRel W.Adj
    W.edgeFinset.card = 3 * Fintype.card V - 6 := by
  classical
  have hV' : 3 ≤ Fintype.card V := by
    first
    | exact hcard
    | (rw [Set.ncard_univ, Nat.card_eq_fintype_card] at hcard; exact hcard)
  have hub : W.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc W hV' hW
  obtain ⟨H0, hGH0, hH0, hle0, hc0⟩ := WilliamsonShmoys.planar_drawing_extension_for_edge_bound_ef555edc W hV' hW
  have hMax0 : ∀ J : SimpleGraph V, H0 ≤ J → HasPlanarDrawingOn J → J ≤ H0 := by
    intro J hHJ hJ
    have hJb := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc J hV' hJ
    have heq := Set.eq_of_subset_of_ncard_le (SimpleGraph.edgeSet_subset_edgeSet.mpr hHJ) (by omega) (Set.toFinite _)
    exact (SimpleGraph.edgeSet_inj.mp heq.symm).le
  have hC0 : H0.Connected := WilliamsonShmoys.maximal_planar_drawingOn_connected H0 hH0 hMax0 hV'
  have hs0 : W.edgeSet ⊆ H0.edgeSet := SimpleGraph.edgeSet_subset_edgeSet.mpr hGH0
  have ha0 : ∀ ⦃u v : V⦄, W.Adj u v → H0.Adj u v := fun u v h => hGH0 h
  have ha0' : ∀ u v : V, W.Adj u v → H0.Adj u v := fun u v h => hGH0 h
  have hes0 : ∀ e, e ∈ W.edgeSet → e ∈ H0.edgeSet := fun e he => hs0 he
  have hR0 : ∀ u v : V, Relation.ReflTransGen H0.Adj u v := fun u v => (SimpleGraph.reachable_iff_reflTransGen _ _).mp (hC0.preconnected u v)
  have hRe0 : ∀ u v : V, H0.Reachable u v := fun u v => hC0.preconnected u v
  have hW0 : ∀ u v : V, Nonempty (H0.Walk u v) := fun u v => hC0.preconnected u v
  have hz0 : (W.edgeSet.ncard : ℤ) ≤ (H0.edgeSet.ncard : ℤ) := by exact_mod_cast hle0
  have hcm0 : 3 * Fintype.card V = H0.edgeSet.ncard + 6 := hc0.symm
  have hcl0 : 3 * Fintype.card V ≤ H0.edgeSet.ncard + 6 := by omega
  have hcs0 : H0.edgeSet.ncard = 3 * Fintype.card V - 6 := by omega
  have hct0 : H0.edgeSet.ncard = 3 * (Fintype.card V - 2) := by omega
  have hct1 : 3 * (Fintype.card V - 2) ≤ H0.edgeSet.ncard := by omega
  have hMax' : ∀ J : SimpleGraph V, W ≤ J → HasPlanarDrawingOn J → J ≤ W := by
    intro J hHJ hJ
    have hs := SimpleGraph.edgeSet_subset_edgeSet.mpr hHJ
    have ha : ∀ ⦃u v : V⦄, W.Adj u v → J.Adj u v := fun u v h => hHJ h
    have ha2 : ∀ u v : V, W.Adj u v → J.Adj u v := fun u v h => hHJ h
    first
    | exact hmax J hHJ hJ
    | exact (hmax J hHJ hJ).le
    | exact (hmax J hHJ hJ).ge
    | exact hmax J hJ hHJ
    | exact (hmax J hJ hHJ).le
    | exact (hmax J hJ hHJ).ge
    | exact SimpleGraph.edgeSet_subset_edgeSet.mp (hmax J hs hJ)
    | exact SimpleGraph.edgeSet_subset_edgeSet.mp (hmax J hJ hs)
    | exact (SimpleGraph.edgeSet_inj.mp (hmax J hs hJ)).le
    | exact (SimpleGraph.edgeSet_inj.mp (hmax J hs hJ)).ge
    | exact (SimpleGraph.edgeSet_inj.mp (hmax J hJ hs)).le
    | exact (SimpleGraph.edgeSet_inj.mp (hmax J hJ hs)).ge
    | exact (hmax J ha hJ).le
    | exact (hmax J ha2 hJ).le
    | exact (hmax J ha hJ).ge
    | exact (hmax J ha2 hJ).ge
    | exact fun u v h => hmax J ha2 hJ u v h
    | exact fun u v h => hmax J ha hJ h
    | exact @hmax J (Classical.decRel _) hHJ hJ
    | exact (@hmax J (Classical.decRel _) hHJ hJ).le
    | exact (@hmax J (Classical.decRel _) hHJ hJ).ge
    | exact @hmax J (Classical.decRel _) hJ hHJ
    | exact (@hmax J (Classical.decRel _) hJ hHJ).le
    | exact (SimpleGraph.edgeSet_inj.mp (Set.eq_of_subset_of_ncard_le hs (hmax J ha hJ) (Set.toFinite _)).symm).le
    | exact (SimpleGraph.edgeSet_inj.mp (Set.eq_of_subset_of_ncard_le hs (hmax J ha2 hJ) (Set.toFinite _)).symm).le
  have hcount : W.edgeSet.ncard + 6 = 3 * Fintype.card V := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc W hV' hW hMax'
  have hconnX : W.Connected := WilliamsonShmoys.maximal_planar_drawingOn_connected W hW hMax' hV'
  first
  | (simp only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, Set.ncard_univ, Nat.card_eq_fintype_card] at *; omega)
  | omega
  | assumption
  | exact hconnX
  | (intro u v; exact (SimpleGraph.reachable_iff_reflTransGen _ _).mp (hconnX.preconnected u v))
  | (refine ⟨H0, ?_⟩; and_intros <;> first | assumption | omega | exact_mod_cast hle0 | (simp only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, Set.ncard_univ, Nat.card_eq_fintype_card] at *; omega) | exact Ne.symm ‹_› | (intro h; exact hnle0 h))
  | (refine ⟨H0, Classical.decRel _, ?_⟩; and_intros <;> first | assumption | omega | exact_mod_cast hle0 | (simp only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, Set.ncard_univ, Nat.card_eq_fintype_card] at *; omega) | exact Ne.symm ‹_› | (intro h; exact hnle0 h))
  | (refine ⟨H0, ?_⟩; first | assumption | omega | exact_mod_cast hle0 | (simp only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, Set.ncard_univ, Nat.card_eq_fintype_card] at *; omega) | exact Ne.symm ‹_› | (intro h; exact hnle0 h))
