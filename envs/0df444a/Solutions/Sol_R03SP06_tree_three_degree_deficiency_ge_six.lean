-- Prove2me | solution 1 for R03SP06.tree_three_degree_deficiency_ge_six
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:03:55.320214+00:00
-- url     : https://prove2.me/submissions/aa520384-d951-4e87-a5f9-443a0aac2c89

import Mathlib

/-!
Candidate formalization of the finite-tree inequality used in the residual
bridge-block argument.  A tree on at least four vertices has total truncated
three-degree deficiency at least six.  This is only the combinatorial tree
part; it does not construct the bridge-block tree of a residual graph.
-/

namespace R03SP06

variable {V : Type} [Fintype V]


end R03SP06

open R03SP06
variable {V : Type} [Fintype V]
theorem solution
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

