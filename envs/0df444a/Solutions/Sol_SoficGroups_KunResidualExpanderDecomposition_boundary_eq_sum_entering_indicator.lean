-- Prove2me | solution 1 for SoficGroups.KunResidualExpanderDecomposition.boundary_eq_sum_entering_indicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/49ca19a7-9e40-4052-9e04-55189e2d516b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_card_entering_eq_card_exiting

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualExpanderDecomposition
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunResidualExpanderDecomposition
theorem _root_.solution {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (A : Finset V) :
    SoficGroups.boundary σ A =
      ∑ i : ι, ∑ x : V,
        if x ∉ A ∧ σ i x ∈ A then 1 else 0 := by
  classical
  unfold SoficGroups.boundary
  apply Finset.sum_congr rfl
  intro i _
  rw [← SoficGroups.KunThomFiberCoarea.card_entering_eq_card_exiting
    (σ i) A, Finset.card_eq_sum_ones, Finset.sum_filter]
end SoficGroups.KunResidualExpanderDecomposition
