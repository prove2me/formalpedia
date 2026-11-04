-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_connected_case__p2m_d560826c_2a6b_46ec_826e_191525151789_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:32:47.229117+00:00
-- url     : https://prove2.me/submissions/39d18003-79dd-4842-821a-34702a1359c0

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hcard : 3 <= Fintype.card V)
    (hlocal : forall s : Finset V, 3 <= s.card ->
      (N.induce (s : Set V)).Connected ->
      (N.induce (s : Set V)).edgeFinset.card <= 3 * s.card - 6)
    (hconn : N.Connected) :
    N.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  classical
  have hcoe : ((Finset.univ : Finset V) : Set V) = (Set.univ : Set V) := by
    ext v
    simp
  have hc : (N.induce ((Finset.univ : Finset V) : Set V)).Connected := by
    rw [hcoe]
    exact N.induceUnivIso.connected_iff.mpr hconn
  have he : (N.induce ((Finset.univ : Finset V) : Set V)).edgeFinset.card =
      N.edgeFinset.card := by
    apply Eq.trans ?_ (SimpleGraph.card_edgeFinset_induce_of_support_subset (G := N)
      (s := ((Finset.univ : Finset V) : Set V)) (by simp))
    apply congrArg Finset.card
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
  have h := hlocal (Finset.univ : Finset V)
    (by simpa only [Finset.card_univ] using hcard) hc
  rw [he, Finset.card_univ] at h
  exact h