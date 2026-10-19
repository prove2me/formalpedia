-- Prove2me | solution 1 for SoficGroups.ComponentMidrankVariance.componentVertexMidrank_finiteVariance_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/964c599f-f13d-4c47-b7fd-99f382ef1568

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ComponentMidrankVariance_componentVertexMidrank_variance_eq
import Theorems.Thm_SoficGroups_ComponentMidrankVariance_componentVertexMidrank_finiteMean_eq_half

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.ComponentMidrankVariance
open scoped BigOperators
namespace SoficGroups.ComponentMidrankVariance
theorem _root_.solution
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (hC : C.Nonempty) :
    SoficGroups.CheegerPoincare.finiteVariance
      (fun x : {x // x ∈ C} =>
        SoficGroups.componentVertexMidrank C b x) =
      SoficGroups.midrankVariance (SoficGroups.componentRankMassList C b) := by
  have hc : (C.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hC
  unfold SoficGroups.CheegerPoincare.finiteVariance
  rw [componentVertexMidrank_finiteMean_eq_half C b hC,
    ← Finset.sum_subtype C (fun _ => Iff.rfl)
      (fun x =>
        (SoficGroups.componentVertexMidrank C b x - (1 / 2 : ℝ)) ^ 2),
    Fintype.card_coe,
    SoficGroups.ComponentMidrankVariance.componentVertexMidrank_variance_eq
      C b hC]
  field_simp
end SoficGroups.ComponentMidrankVariance
