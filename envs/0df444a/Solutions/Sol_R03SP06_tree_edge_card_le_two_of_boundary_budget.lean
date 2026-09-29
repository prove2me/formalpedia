-- Prove2me | solution 1 for R03SP06.tree_edge_card_le_two_of_boundary_budget
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:48:04.617095+00:00
-- url     : https://prove2.me/submissions/ac84155a-421f-4166-a0fc-79c60ac5945b

import Mathlib

/-!
Candidate formalization of the finite-tree inequality used in the residual
bridge-block argument.  A tree on at least four vertices has total truncated
three-degree deficiency at least six.  This is only the combinatorial tree
part; it does not construct the bridge-block tree of a residual graph.
-/

namespace R03SP06

variable {V : Type} [Fintype V]

/-- A tree on at least four vertices satisfies the deficiency bound appearing
in the candidate residual bridge argument. -/
theorem tree_three_degree_deficiency_ge_six
    {T : SimpleGraph V} [DecidableRel T.Adj]
    (hT : T.IsTree) (hcard : 4 ≤ Fintype.card V) :
    6 ≤ ∑ v : V, (3 - T.degree v) := by
  have hpoint : ∀ v : V, 3 ≤ (3 - T.degree v) + T.degree v := by
    intro v
    omega
  have hsum_ineq :
      ∑ _v : V, 3 ≤ ∑ v : V, ((3 - T.degree v) + T.degree v) := by
    apply Finset.sum_le_sum
    intro v hv
    exact hpoint v
  have hsum : ∑ v : V, T.degree v = 2 * T.edgeFinset.card :=
    T.sum_degrees_eq_twice_card_edges
  have htree : T.edgeFinset.card + 1 = Fintype.card V :=
    hT.card_edgeFinset
  rw [Finset.sum_add_distrib, hsum] at hsum_ineq
  simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] at hsum_ineq
  omega

#print axioms R03SP06.tree_three_degree_deficiency_ge_six


end R03SP06

open R03SP06
variable {V : Type} [Fintype V]
theorem solution
    {T : SimpleGraph V} [DecidableRel T.Adj]
    (hT : T.IsTree) {r : V → Nat}
    (hbound : ∀ v : V, 3 - T.degree v ≤ r v)
    (hsum : ∑ v : V, r v ≤ 5) :
    T.edgeFinset.card ≤ 2 := by
  by_contra hnot
  have hE : 3 ≤ T.edgeFinset.card := by omega
  have htree : T.edgeFinset.card + 1 = Fintype.card V :=
    hT.card_edgeFinset
  have hcard : 4 ≤ Fintype.card V := by omega
  have hdef : 6 ≤ ∑ v : V, (3 - T.degree v) :=
    tree_three_degree_deficiency_ge_six hT hcard
  have hsumle :
      (∑ v : V, (3 - T.degree v)) ≤ ∑ v : V, r v := by
    apply Finset.sum_le_sum
    intro v hv
    exact hbound v
  omega

