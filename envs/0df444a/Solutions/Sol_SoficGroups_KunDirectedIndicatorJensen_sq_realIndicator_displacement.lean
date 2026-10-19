-- Prove2me | solution 1 for SoficGroups.KunDirectedIndicatorJensen.sq_realIndicator_displacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/7cf0e398-43d0-418f-8188-bc2bba6dc34f

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDirectedIndicatorJensen
open scoped BigOperators
namespace SoficGroups.KunDirectedIndicatorJensen
theorem _root_.solution
    {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (T : Finset V) (x : V) :
    (realIndicator T (p x) - realIndicator T x) ^ 2 =
      (if x ∈ T ∧ p x ∉ T then (1 : ℝ) else 0) +
      (if x ∉ T ∧ p x ∈ T then (1 : ℝ) else 0) := by
  classical
  by_cases hx : x ∈ T <;> by_cases hp : p x ∈ T <;>
    simp [realIndicator, hx, hp]
end SoficGroups.KunDirectedIndicatorJensen
