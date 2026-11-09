-- Prove2me | solution 1 for TenChallenges.caccettaHaggkvist_dense
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:36:00.271668+00:00
-- url     : https://prove2.me/submissions/e7cef001-1d7a-4100-bbe6-d2b611d4733f

import Definitions.Def_TenChallenges_Challenge_03
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace TenChallenges.Continuation

open Finset

variable {V : Type} [Fintype V]

omit [Fintype V] in
/-- A mutual pair of arcs gives a directed cycle of length two. -/
theorem hasCycleOfLength_two_of_mutual (G : Digraph V) {a b : V}
    (hne : a ≠ b) (hab : G.Adj a b) (hba : G.Adj b a) :
    G.HasCycleOfLength 2 := by
  refine ⟨![a, b], ?_, ?_⟩
  · simp [Function.Injective, Fin.forall_fin_succ, hne, hne.symm]
  · simpa [Fin.forall_fin_succ, finRotate_apply] using And.intro hab hba

/-- The outdegree of any vertex of a finite loopless digraph is below the order. -/
theorem outDegree_lt_card (G : Digraph V) (hloop : ∀ v, ¬ G.Adj v v) (v : V) :
    G.outDegree v < Fintype.card V := by
  simpa only [Digraph.outDegree, Nat.card_eq_fintype_card] using
    Set.ncard_lt_card (s := {w | G.Adj v w})
      (fun h => hloop v ((Set.ext_iff.mp h v).mpr (Set.mem_univ v)))

/-- In a loopless digraph, minimum outdegree at least half the order forces a 2-cycle. -/
theorem hasCycleOfLength_two_of_dense [Nonempty V] (G : Digraph V) (r : ℕ)
    (hloop : ∀ v, ¬ G.Adj v v) (hdeg : ∀ v, r ≤ G.outDegree v)
    (hcard : Fintype.card V ≤ 2 * r) : G.HasCycleOfLength 2 := by
  classical
  by_contra hcycle
  have hno (a b : V) (hab : G.Adj a b) : ¬ G.Adj b a :=
    fun hba => hcycle (hasCycleOfLength_two_of_mutual G
      (fun e : a = b => hloop b (e ▸ hab)) hab hba)
  have hout (v : V) : r ≤ (univ.bipartiteAbove G.Adj v).card := by
    simpa [Digraph.outDegree, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred,
      bipartiteAbove] using hdeg v
  have hin (v : V) : (univ.bipartiteBelow G.Adj v).card < r := by
    have hd : Disjoint (univ.bipartiteAbove G.Adj v)
        (univ.bipartiteBelow G.Adj v) := by
      exact disjoint_left.mpr (fun w hw₁ hw₂ => hno v w
        ((mem_bipartiteAbove G.Adj).mp hw₁).2 ((mem_bipartiteBelow G.Adj).mp hw₂).2)
    have hnot : v ∉ univ.bipartiteAbove G.Adj v ∪
        univ.bipartiteBelow G.Adj v := by
      simp [hloop v]
    have hb := card_le_card (subset_univ (insert v
      (univ.bipartiteAbove G.Adj v ∪ univ.bipartiteBelow G.Adj v)))
    rw [card_insert_of_notMem hnot, card_union_of_disjoint hd, card_univ] at hb
    have hv := hout v
    omega
  exact (lt_irrefl ((univ : Finset V).card • r))
    (card_nsmul_lt_card_nsmul_of_le_of_lt G.Adj univ_nonempty
      (fun v _ => hout v) (fun v _ => hin v))

/-- The Caccetta–Häggkvist conclusion holds whenever the order is at most twice the
minimum-outdegree parameter. This covers the first nonvacuous orders for `r = 2`. -/
theorem caccettaHaggkvist_of_dense [Nonempty V] (G : Digraph V) (r : ℕ)
    (hloop : ∀ v, ¬ G.Adj v v) (hdeg : ∀ v, r ≤ G.outDegree v)
    (hcard : Fintype.card V ≤ 2 * r) :
    ∃ ℓ, 2 ≤ ℓ ∧ ℓ * r < Fintype.card V + r ∧ G.HasCycleOfLength ℓ := by
  have hlt := (hdeg (Classical.arbitrary V)).trans_lt
    (outDegree_lt_card G hloop (Classical.arbitrary V))
  exact ⟨2, le_rfl, by omega, hasCycleOfLength_two_of_dense G r hloop hdeg hcard⟩

/-- Challenge 03 at minimum outdegree two, restricted to digraphs of order at most four. -/
theorem caccettaHaggkvist_two_of_card_le_four [Nonempty V] (G : Digraph V)
    (hloop : ∀ v, ¬ G.Adj v v) (hdeg : ∀ v, 2 ≤ G.outDegree v)
    (hcard : Fintype.card V ≤ 4) :
    ∃ ℓ, 2 ≤ ℓ ∧ ℓ * 2 < Fintype.card V + 2 ∧ G.HasCycleOfLength ℓ :=
  caccettaHaggkvist_of_dense G 2 hloop hdeg hcard

end TenChallenges.Continuation



theorem solution (r : ℕ) {V : Type} [Fintype V] [Nonempty V] (G : Digraph V)
    (hloop : ∀ v, ¬ G.Adj v v) (hdeg : ∀ v, r ≤ G.outDegree v)
    (hcard : Fintype.card V ≤ 2 * r) :
    ∃ ℓ, 2 ≤ ℓ ∧ ℓ * r < Fintype.card V + r ∧ G.HasCycleOfLength ℓ :=
  TenChallenges.Continuation.caccettaHaggkvist_of_dense G r hloop hdeg hcard

#print axioms solution
