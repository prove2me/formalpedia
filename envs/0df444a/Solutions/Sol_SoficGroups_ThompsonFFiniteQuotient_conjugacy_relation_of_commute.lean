-- Prove2me | solution 1 for SoficGroups.ThompsonFFiniteQuotient.conjugacy_relation_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/cbc30501-5278-45a6-8752-7562b98554b7

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ThompsonFFiniteQuotient_conjugateTerm_succ

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFFiniteQuotient
variable {G : Type*} [Group G]
namespace SoficGroups.ThompsonFFiniteQuotient
theorem _root_.solution (a b : G) (n : ℕ)
    (h : Commute (a * b⁻¹) (conjugateTerm a b n)) :
    b⁻¹ * conjugateTerm a b n * b =
      conjugateTerm a b (n + 1) := by
  rw [conjugateTerm_succ]
  calc
    b⁻¹ * conjugateTerm a b n * b =
        a⁻¹ * ((a * b⁻¹) * conjugateTerm a b n) * b := by
      group
    _ = a⁻¹ * (conjugateTerm a b n * (a * b⁻¹)) * b := by
      rw [h.eq]
    _ = a⁻¹ * conjugateTerm a b n * a := by
      group
end SoficGroups.ThompsonFFiniteQuotient
