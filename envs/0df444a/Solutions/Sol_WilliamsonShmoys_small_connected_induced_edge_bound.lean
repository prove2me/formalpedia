-- Prove2me | solution 1 for WilliamsonShmoys.small_connected_induced_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T18:52:55.598516+00:00
-- url     : https://prove2.me/submissions/49f11a1a-2308-46de-880b-d53e29b51f60

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (C : Finset V)
    (hC : C.Nonempty)
    (hconn : (G.induce (fun v => v ∈ C)).Connected)
    (hsmall : C.card < 3) :
    (G.induce (fun v => v ∈ C)).edgeSet.ncard ≤ 3 * C.card - 3 := by
  classical
  have h1 := (G.induce (fun v => v ∈ C)).card_edgeFinset_le_card_choose_two
  rw [Set.ncard_eq_toFinset_card' (G.induce (fun v => v ∈ C)).edgeSet]
  rw [← SimpleGraph.edgeFinset] at *
  have hc : Fintype.card {v // v ∈ C} = C.card := Fintype.card_coe C
  have hpos := hC.card_pos
  have h2 : (G.induce (fun v => v ∈ C)).edgeFinset.card ≤ C.card.choose 2 := by
    rw [Fintype.card_subtype] at h1
    refine h1.trans (le_of_eq ?_)
    congr 2
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  interval_cases h : C.card <;> simp_all <;> omega
