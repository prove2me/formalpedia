-- Prove2me | solution 1 for SoficGroups.KunDirectedIndicatorJensen.sum_sq_realIndicator_displacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/c3224325-7722-48dd-b03f-6136b634bc2b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_card_entering_eq_card_exiting
import Theorems.Thm_SoficGroups_KunDirectedIndicatorJensen_sq_realIndicator_displacement

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDirectedIndicatorJensen
open scoped BigOperators
namespace SoficGroups.KunDirectedIndicatorJensen
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (T : Finset V) :
    (∑ x : V,
      (realIndicator T (p x) - realIndicator T x) ^ 2) =
      2 * ((T.filter fun x => p x ∉ T).card : ℝ) := by
  classical
  simp_rw [sq_realIndicator_displacement]
  rw [Finset.sum_add_distrib]
  have hleave :
      (∑ x : V,
        if x ∈ T ∧ p x ∉ T then (1 : ℝ) else 0) =
        ((T.filter fun x => p x ∉ T).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
    congr 1
    ext x
    simp
  have henter :
      (∑ x : V,
        if x ∉ T ∧ p x ∈ T then (1 : ℝ) else 0) =
        ((Finset.univ.filter fun x => x ∉ T ∧ p x ∈ T).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [hleave, henter,
    SoficGroups.KunThomFiberCoarea.card_entering_eq_card_exiting]
  ring
end SoficGroups.KunDirectedIndicatorJensen
