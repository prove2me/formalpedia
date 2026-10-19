-- Prove2me | solution 1 for SoficGroups.CheegerPoincare.card_mul_finiteVariance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/ff409a8f-5b2a-414f-b166-d8ba0b7d0016

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.CheegerPoincare
open scoped BigOperators
namespace SoficGroups.CheegerPoincare
theorem _root_.solution {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ) :
    (Fintype.card V : ℝ) * finiteVariance f =
      ∑ x : V, (f x - finiteMean f) ^ 2 := by
  have hc : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold finiteVariance
  field_simp
end SoficGroups.CheegerPoincare
