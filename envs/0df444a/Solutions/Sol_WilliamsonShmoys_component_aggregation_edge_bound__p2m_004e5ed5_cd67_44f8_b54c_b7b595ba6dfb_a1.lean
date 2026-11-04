-- Prove2me | solution 1 for WilliamsonShmoys.component_aggregation_edge_bound__p2m_004e5ed5_cd67_44f8_b54c_b7b595ba6dfb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T21:15:56.982209+00:00
-- url     : https://prove2.me/submissions/cf61253f-79cc-4e88-bf88-e9d775c63404

import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarDrawing_edgeUpper_of_induced_bounds

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hcard : 3 ≤ Fintype.card V)
    (hcomp : ∀ S : Finset V, 3 ≤ S.card →
      (U.induce (↑S : Set V)).Connected →
      (letI : DecidableRel (U.induce (↑S : Set V)).Adj := Classical.decRel _
       (U.induce (↑S : Set V)).edgeFinset.card ≤ 3 * S.card - 6)) :
    (letI : DecidableRel U.Adj := dU
     U.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  classical
  letI : DecidableRel U.Adj := dU
  have hb : ∀ S : Finset V,
      (U.induce (↑S : Set V)).Connected →
      3 ≤ Fintype.card S →
      (U.induce (↑S : Set V)).edgeSet.ncard + 6 ≤ 3 * Fintype.card S := by
    intro S hc hs
    letI : DecidableRel (U.induce (↑S : Set V)).Adj := Classical.decRel _
    have hs' : 3 ≤ S.card := by simpa using hs
    have h := hcomp S hs' hc
    have he : (U.induce (↑S : Set V)).edgeSet.ncard =
        (U.induce (↑S : Set V)).edgeFinset.card := by
      rw [Set.ncard_eq_toFinset_card']
      rfl
    rw [he]
    have hsize : Fintype.card S = S.card := by simp
    rw [hsize]
    omega
  have h := WilliamsonShmoys.planarDrawing_edgeUpper_of_induced_bounds U hb hcard
  have he : U.edgeSet.ncard = U.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  rw [he] at h
  omega
