-- Prove2me | solution 1 for WilliamsonShmoys.planar_component_bounds_sum__p2m_fd05939c_3060_4687_b686_08bcaa4f6cdd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:30:37.503917+00:00
-- url     : https://prove2.me/submissions/f2878213-98db-4ecb-836f-93ee773e1792

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_partition_card_sum_of_disjoint_cover__p2m_9b39c159_5abf_402e_b341_b70b3524bea9_a1
import Theorems.Thm_WilliamsonShmoys_nat_sum_component_edge_bounds__p2m_9b39c159_5abf_402e_b341_b70b3524bea9_a1

set_option autoImplicit false

open Finset

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (C : V → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hcover : Finset.univ.biUnion C = Finset.univ)
    (hedges : L.edgeSet.ncard = ∑ i : V, (L.induce (fun v => v ∈ C i)).edgeSet.ncard)
    (hlocal : ∀ i,
      if 3 ≤ (C i).card then
        (L.induce (fun v => v ∈ C i)).edgeSet.ncard ≤ 3 * (C i).card - 6
      else if 2 ≤ (C i).card then
        (L.induce (fun v => v ∈ C i)).edgeSet.ncard ≤ 1
      else
        (L.induce (fun v => v ∈ C i)).edgeSet.ncard = 0)
    (hcard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  let s : V → ℕ := fun i => (C i).card
  let a : V → ℕ := fun i => (L.induce (fun v => v ∈ C i)).edgeSet.ncard
  have hsumcard : (∑ i : V, s i) = Fintype.card V := by
    exact WilliamsonShmoys.partition_card_sum_of_disjoint_cover__p2m_9b39c159_5abf_402e_b341_b70b3524bea9_a1 C hdisj hcover
  have hsumsize : 3 ≤ ∑ i : V, s i := by
    rw [hsumcard]
    exact hcard
  have hsumedges : (∑ i : V, a i) ≤ 3 * (∑ i : V, s i) - 6 :=
    WilliamsonShmoys.nat_sum_component_edge_bounds__p2m_9b39c159_5abf_402e_b341_b70b3524bea9_a1 s a hsumsize (by intro i; simpa [s, a] using hlocal i)
  calc
    L.edgeSet.ncard = ∑ i : V, a i := by simpa [a] using hedges
    _ ≤ 3 * (∑ i : V, s i) - 6 := hsumedges
    _ = 3 * Fintype.card V - 6 := by rw [hsumcard]