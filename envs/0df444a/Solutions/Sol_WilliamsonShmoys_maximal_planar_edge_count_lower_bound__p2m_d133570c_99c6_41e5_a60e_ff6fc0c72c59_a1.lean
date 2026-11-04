-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_d133570c_99c6_41e5_a60e_ff6fc0c72c59_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:04:51.384695+00:00
-- url     : https://prove2.me/submissions/5026b26b-6da4-4905-90a6-19a297533b01

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_can_be_strictly_augmented_when_below_bound__p2m_300e589a_9958_4177_9a18_5a010b7286b4_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, K ≤ M → HasPlanarDrawingOn M → M ≤ K) :
    (letI : DecidableRel K.Adj := dK;
      3 * Fintype.card V - 6 ≤ K.edgeFinset.card) := by
  letI : DecidableRel K.Adj := dK
  change 3 * Fintype.card V - 6 ≤ K.edgeFinset.card
  by_contra hnot
  have hlt : K.edgeFinset.card < 3 * Fintype.card V - 6 := by omega
  obtain ⟨M, hKM, hproper, hM⟩ :=
    WilliamsonShmoys.planar_drawing_can_be_strictly_augmented_when_below_bound__p2m_300e589a_9958_4177_9a18_5a010b7286b4_a1
      K dK hK hcard hlt
  exact hproper (hmax M hKM hM)