-- Prove2me | solution 1 for SoficGroups.CheegerPoincare.positiveSupport_max_sub_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/f24dbfb0-4eae-4904-8d99-f0984a9566c7

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_CheegerPoincare_positive_max_iff

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
    (f : V → ℝ) (m : ℝ) :
    positiveSupport (fun x => max (m - f x) 0) = lowerLevel f m := by
  classical
  ext x
  simp only [mem_positiveSupport, mem_lowerLevel,
    positive_max_iff, sub_pos]
end SoficGroups.CheegerPoincare
