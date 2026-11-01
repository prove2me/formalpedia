-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_can_be_strictly_augmented_when_below_bound__p2m_300e589a_9958_4177_9a18_5a010b7286b4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:03:32.16118+00:00
-- url     : https://prove2.me/submissions/dd63c053-cc69-4d0b-8423-82d9cc596f7c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_17cdf377_ddf7_4ef9_90d4_89407a0a5949_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_17cdf377_ddf7_4ef9_90d4_89407a0a5949_a2
import Theorems.Thm_WilliamsonShmoys_edgeFinset_card_independent_of_decidableRel__p2m_17cdf377_ddf7_4ef9_90d4_89407a0a5949_a4
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := dK;
      K.edgeFinset.card < 3 * Fintype.card V - 6) →
      ∃ M : SimpleGraph V, K ≤ M ∧ ¬ M ≤ K ∧ HasPlanarDrawingOn M := by
  classical
  letI : DecidableRel K.Adj := dK
  intro hsmall
  obtain ⟨M, hKM, hMdraw, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_17cdf377_ddf7_4ef9_90d4_89407a0a5949_a2
      K hK
  letI : DecidableRel M.Adj := Classical.decRel _
  have hMcard :=
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_17cdf377_ddf7_4ef9_90d4_89407a0a5949_a2
      M (Classical.decRel _) hMdraw hcard hmax
  have hne : M ≠ K := by
    intro heq
    subst M
    have hdecCard :=
      WilliamsonShmoys.edgeFinset_card_independent_of_decidableRel__p2m_17cdf377_ddf7_4ef9_90d4_89407a0a5949_a4
        K (Classical.decRel _) dK
    rw [hdecCard] at hMcard
    rw [hMcard] at hsmall
    exact Nat.lt_irrefl _ hsmall
  refine ⟨M, hKM, ?_, hMdraw⟩
  intro hMK
  exact hne (le_antisymm hMK hKM)
