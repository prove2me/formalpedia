-- Prove2me | solution 1 for SoficGroups.CheegerPoincare.positiveSupport_max_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/286f0a6f-1592-4de5-b4e7-42c6bf7f2759

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
    positiveSupport (fun x => max (f x - m) 0) = upperLevel f m := by
  classical
  ext x
  simp only [mem_positiveSupport, mem_upperLevel,
    positive_max_iff, sub_pos]
end SoficGroups.CheegerPoincare
