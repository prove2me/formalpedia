-- Prove2me | solution 1 for SoficGroups.KunResidualExpanderDecomposition.boundary_complement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/64e08151-df98-49d4-b726-cd6e70fbdf36

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_boundary_eq_sum_indicator
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_boundary_eq_sum_entering_indicator

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
    SoficGroups.boundary σ (Finset.univ \ A) =
      SoficGroups.boundary σ A := by
  rw [boundary_eq_sum_indicator σ (Finset.univ \ A),
    boundary_eq_sum_entering_indicator σ A]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  simp
end SoficGroups.KunResidualExpanderDecomposition
