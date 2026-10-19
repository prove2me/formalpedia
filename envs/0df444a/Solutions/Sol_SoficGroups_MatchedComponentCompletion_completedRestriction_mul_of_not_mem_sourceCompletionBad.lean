-- Prove2me | solution 1 for SoficGroups.MatchedComponentCompletion.completedRestriction_mul_of_not_mem_sourceCompletionBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/050991c2-d245-43dc-9d70-db4e0b361337

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_CompressionCriterion_mem_productTrackedTable
import Theorems.Thm_SoficGroups_CompressionCriterion_mul_mem_productTrackedTable
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_sourceCompletionBad_good

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentCompletion
open scoped BigOperators
namespace SoficGroups.MatchedComponentCompletion
theorem _root_.solution
    {V ι J : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V)
    {j k : J} (hj : j ∈ F) (hk : k ∈ F)
    (z : {x : V // x ∈ Z})
    (hz : (z : V) ∉ sourceCompletionBad σ p F Z) :
    completedRestriction (p (j * k)) Z z =
      (completedRestriction (p j) Z * completedRestriction (p k) Z) z := by
  have hg := sourceCompletionBad_good σ p F Z z z.property hz
  have hjT :=
    SoficGroups.CompressionCriterion.mem_productTrackedTable hj
  have hkT :=
    SoficGroups.CompressionCriterion.mem_productTrackedTable hk
  have hjkT :=
    SoficGroups.CompressionCriterion.mul_mem_productTrackedTable hj hk
  have hkZ : p k (z : V) ∈ Z := hg.2.1 k hkT
  have hjkZ : p (j * k) (z : V) ∈ Z := hg.2.1 (j * k) hjkT
  have hmul : p (j * k) (z : V) = p j (p k (z : V)) :=
    hg.2.2.2.2.1 j hj k hk
  have hinner : p j (p k (z : V)) ∈ Z := by
    rw [← hmul]
    exact hjkZ
  have hkvalue :
      ((completedRestriction (p k) Z z : {x : V // x ∈ Z}) : V) =
        p k (z : V) :=
    completedRestriction_apply_of_mem (p k) Z z z.property hkZ
  apply Subtype.ext
  change
    ((completedRestriction (p (j * k)) Z z : {x : V // x ∈ Z}) : V) =
      ((completedRestriction (p j) Z
        (completedRestriction (p k) Z z) : {x : V // x ∈ Z}) : V)
  calc
    ((completedRestriction (p (j * k)) Z z : {x : V // x ∈ Z}) : V) =
        p (j * k) (z : V) :=
      completedRestriction_apply_of_mem (p (j * k)) Z z z.property hjkZ
    _ = p j (p k (z : V)) := hmul
    _ = p j
        ((completedRestriction (p k) Z z : {x : V // x ∈ Z}) : V) := by
      rw [hkvalue]
    _ = ((completedRestriction (p j) Z
        (completedRestriction (p k) Z z) : {x : V // x ∈ Z}) : V) := by
      symm
      apply completedRestriction_apply_of_mem
      change
        p j ((completedRestriction (p k) Z z :
          {x : V // x ∈ Z}) : V) ∈ Z
      rw [hkvalue]
      exact hinner
end SoficGroups.MatchedComponentCompletion
