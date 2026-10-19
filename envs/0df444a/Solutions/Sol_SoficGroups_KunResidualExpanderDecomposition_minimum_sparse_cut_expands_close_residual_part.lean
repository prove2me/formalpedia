-- Prove2me | solution 1 for SoficGroups.KunResidualExpanderDecomposition.minimum_sparse_cut_expands_close_residual_part
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/22f9ee84-78c1-44c7-8ec8-019d251b7e50

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_close_residual_inter_properties

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualExpanderDecomposition
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunResidualExpanderDecomposition
theorem _root_.solution
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (R T U : Finset V) (γ : ℝ)
    (hTR : T ⊆ R)
    (hminimum : ∀ E : Finset V, E ⊆ R →
      (SoficGroups.boundary σ E : ℝ) < γ * (E.card : ℝ) →
      T.card ≤ E.card)
    (hclose : 3 * (U ∆ T).card < T.card) :
    ∀ E : Finset V, E ⊆ R ∩ U →
      2 * E.card ≤ (R ∩ U).card →
      γ * (E.card : ℝ) ≤ (SoficGroups.boundary σ E : ℝ) := by
  intro E hE hhalf
  by_contra h
  have hbad :
      (SoficGroups.boundary σ E : ℝ) < γ * (E.card : ℝ) :=
    lt_of_not_ge h
  have hER : E ⊆ R := hE.trans Finset.inter_subset_left
  have hmin := hminimum E hER hbad
  have hsize := (close_residual_inter_properties R T U hTR hclose).2.2
  omega
end SoficGroups.KunResidualExpanderDecomposition
