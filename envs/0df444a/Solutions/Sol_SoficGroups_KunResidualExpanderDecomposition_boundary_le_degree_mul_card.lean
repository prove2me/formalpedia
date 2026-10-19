-- Prove2me | solution 1 for SoficGroups.KunResidualExpanderDecomposition.boundary_le_degree_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/ff188115-cc14-4d92-9413-e6e1a5c40eb6

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualExpanderDecomposition
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunResidualExpanderDecomposition
theorem _root_.solution {V ι : Type*}
    [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (A : Finset V) :
    SoficGroups.boundary σ A ≤ Fintype.card ι * A.card := by
  unfold SoficGroups.boundary
  calc
    (∑ i : ι, (A.filter fun x => σ i x ∉ A).card) ≤
        ∑ _i : ι, A.card := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.card_filter_le _ _
    _ = Fintype.card ι * A.card := by
      simp
end SoficGroups.KunResidualExpanderDecomposition
