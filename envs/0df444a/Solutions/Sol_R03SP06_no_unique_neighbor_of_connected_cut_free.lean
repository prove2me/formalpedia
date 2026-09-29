-- Prove2me | solution 1 for R03SP06.no_unique_neighbor_of_connected_cut_free
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:48:00.709944+00:00
-- url     : https://prove2.me/submissions/ca691112-ec30-4011-9f42-f8a352a15cb1

import Mathlib
import Definitions.Def_cubic_p3_partition_models

/-!
Candidate-only graph-connectivity lemma for the q=3 residual branch.
A connected graph of order at least three in which deletion of every vertex
remains connected cannot contain a vertex with a unique neighbor.  The lemma
is deliberately phrased without a degree API so that it can be applied to
induced residual graphs after their graph-specific connectivity reduction.
-/

namespace R03SP06

variable {V : Type} [Fintype V] [DecidableEq V]


end R03SP06

open R03SP06
variable {V : Type} [Fintype V] [DecidableEq V]
theorem solution
    {G : SimpleGraph V}
    (hcard : 3 ≤ Fintype.card V)
    (hconn : G.Connected)
    (hcut : ∀ x : V, (G.induce {v : V | v ≠ x}).Connected) :
    ¬ ∃ v u : V, G.Adj v u ∧ ∀ w : V, G.Adj v w → w = u := by
  rintro ⟨v, u, hvu, hunique⟩
  have hvne : v ≠ u := by
    intro h
    subst u
    exact G.loopless.irrefl v hvu
  have htwo : 2 ≤ (Finset.univ.erase v).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v)]
    simp
    omega
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hex : ∃ w ∈ Finset.univ.erase v, w ≠ u := by
    by_contra h
    push_neg at h
    have hsub : Finset.univ.erase v ⊆ ({u} : Finset V) := by
      intro w hw
      exact Finset.mem_singleton.mpr (h w hw)
    have hle : (Finset.univ.erase v).card ≤ 1 := by
      exact (Finset.card_le_one_iff_subset_singleton.mpr ⟨u, hsub⟩)
    omega
  obtain ⟨w, hw, hwu⟩ := hex
  have hwv : w ≠ v := by
    intro h
    exact (Finset.mem_erase.mp hw).1 h
  let H : SimpleGraph {x : V // x ≠ u} := G.induce {x : V | x ≠ u}
  let v' : {x : V // x ≠ u} := ⟨v, hvne⟩
  let w' : {x : V // x ≠ u} := ⟨w, hwu⟩
  have hvw' : v' ≠ w' := by
    intro h
    exact hwv (congrArg Subtype.val h).symm
  letI : Fintype (H.neighborSet v') := Fintype.ofFinite _
  have hdeg0 : H.degree v' = 0 := by
    rw [SimpleGraph.degree_eq_zero]
    intro z hz
    have hzG : G.Adj v z.1 := by
      exact (SimpleGraph.induce_adj.mp hz)
    have hzu : z.1 = u := hunique z.1 hzG
    exact z.property hzu
  have hreach : H.Reachable v' w' := by
    exact (hcut u).preconnected v' w'
  exact (SimpleGraph.not_reachable_of_left_degree_zero hvw' hdeg0) hreach

