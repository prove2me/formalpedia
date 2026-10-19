-- Prove2me | solution 1 for SoficGroups.ComponentMidrankVariance.componentVertexMidrank_finiteMean_eq_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/46304a7e-8159-421f-995f-687760ded91e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ComponentMidrankVariance_sum_componentVertexMidrank

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
    SoficGroups.CheegerPoincare.finiteMean
      (fun x : {x // x ∈ C} =>
        SoficGroups.componentVertexMidrank C b x) =
      (1 / 2 : ℝ) := by
  have hc : (C.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hC
  unfold SoficGroups.CheegerPoincare.finiteMean
  rw [← Finset.sum_subtype C (fun _ => Iff.rfl)
    (SoficGroups.componentVertexMidrank C b),
    Fintype.card_coe,
    SoficGroups.ComponentMidrankVariance.sum_componentVertexMidrank C b hC]
  field_simp
end SoficGroups.ComponentMidrankVariance
