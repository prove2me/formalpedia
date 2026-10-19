-- Prove2me | solution 1 for SoficGroups.ThompsonFFiniteQuotient.finite_group_commute_of_thompsonF_two_relations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/3247ad3c-41d3-413a-ac90-a977f59078dd

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ThompsonFFiniteQuotient_conjugateTerm_succ
import Theorems.Thm_SoficGroups_ThompsonFFiniteQuotient_conjugacy_relation_of_commute
import Theorems.Thm_SoficGroups_ThompsonFFiniteQuotient_conjugacy_relation_all

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFFiniteQuotient
variable {G : Type*} [Group G]
namespace SoficGroups.ThompsonFFiniteQuotient
theorem _root_.solution
    {G : Type*} [Group G] [Finite G] (a b : G)
    (hfirst : Commute (a * b⁻¹) (a⁻¹ * b * a))
    (hsecond : Commute (a * b⁻¹) ((a ^ 2)⁻¹ * b * a ^ 2)) :
    Commute a b := by
  have hfirst' : b⁻¹ * conjugateTerm a b 1 * b =
      conjugateTerm a b 2 := by
    apply conjugacy_relation_of_commute a b 1
    simpa [conjugateTerm] using hfirst
  have hsecond' : b⁻¹ * conjugateTerm a b 2 * b =
      conjugateTerm a b 3 := by
    apply conjugacy_relation_of_commute a b 2
    simpa [conjugateTerm] using hsecond
  have hpositive : 0 < orderOf a := orderOf_pos a
  have hindex : orderOf a - 1 + 1 = orderOf a :=
    Nat.sub_add_cancel hpositive
  have hnext : orderOf a - 1 + 2 = orderOf a + 1 := by
    omega
  have hperiod : conjugateTerm a b (orderOf a) = b := by
    simp [conjugateTerm, pow_orderOf_eq_one]
  have hconjugate :
      conjugateTerm a b (orderOf a + 1) = a⁻¹ * b * a := by
    rw [conjugateTerm_succ, hperiod]
  have hrelation := conjugacy_relation_all a b hfirst' hsecond'
    (orderOf a - 1)
  rw [hindex, hnext, hperiod, hconjugate] at hrelation
  have heq : b = a⁻¹ * b * a := by
    simpa using hrelation
  change a * b = b * a
  calc
    a * b = a * (a⁻¹ * b * a) := congrArg (fun z : G => a * z) heq
    _ = b * a := by group
end SoficGroups.ThompsonFFiniteQuotient
