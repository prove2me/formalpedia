-- Prove2me | solution 1 for SoficGroups.CheegerPoincare.finiteVariance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/7823d822-234f-4ab9-9323-55b0a19c70d2

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
theorem _root_.solution {V : Type*} [Fintype V]
    (f : V → ℝ) : 0 ≤ finiteVariance f := by
  unfold finiteVariance
  exact div_nonneg
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Nat.cast_nonneg _)
end SoficGroups.CheegerPoincare
