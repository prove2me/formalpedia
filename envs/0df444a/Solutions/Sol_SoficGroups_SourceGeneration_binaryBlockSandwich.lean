-- Prove2me | solution 1 for SoficGroups.SourceGeneration.binaryBlockSandwich
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/5f33b0c1-2845-42fa-9acb-c8b47c855f73

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.SourceGeneration
open scoped commutatorElement
namespace SoficGroups.SourceGeneration
theorem _root_.solution
    (x₀ x₁ y₀ y₁ a : BinaryLeavitt) (p q : Fin 2) :
    (x₀ * leavittT 0 + x₁ * leavittT 1) *
        (leavittS p * a * leavittT q) *
        (leavittS 0 * y₀ + leavittS 1 * y₁) =
      (if p = 0 then x₀ else x₁) * a *
        (if q = 0 then y₀ else y₁) := by
  have hact (r s : Fin 2) (x : BinaryLeavitt) :
      leavittT r * (leavittS s * x) = if r = s then x else 0 := by
    rw [← mul_assoc, leavittT_mul_S]
    split <;> simp
  fin_cases p <;> fin_cases q <;>
    simp [add_mul, mul_add, mul_assoc, hact]
end SoficGroups.SourceGeneration
