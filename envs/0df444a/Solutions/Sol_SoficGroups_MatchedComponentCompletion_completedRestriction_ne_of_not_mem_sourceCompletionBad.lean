-- Prove2me | solution 1 for SoficGroups.MatchedComponentCompletion.completedRestriction_ne_of_not_mem_sourceCompletionBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/1e212150-f1c3-4175-90d2-2068a0a248a8

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_CompressionCriterion_mem_productTrackedTable
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
    {j k : J} (hj : j ∈ F) (hk : k ∈ F) (hne : j ≠ k)
    (z : {x : V // x ∈ Z})
    (hz : (z : V) ∉ sourceCompletionBad σ p F Z) :
    completedRestriction (p j) Z z ≠ completedRestriction (p k) Z z := by
  have hg := sourceCompletionBad_good σ p F Z z z.property hz
  have hjT :=
    SoficGroups.CompressionCriterion.mem_productTrackedTable hj
  have hkT :=
    SoficGroups.CompressionCriterion.mem_productTrackedTable hk
  have hjZ : p j (z : V) ∈ Z := hg.2.1 j hjT
  have hkZ : p k (z : V) ∈ Z := hg.2.1 k hkT
  intro heq
  apply hg.2.2.2.2.2 j hj k hk hne
  have hval := congrArg
    (fun x : {x : V // x ∈ Z} => (x : V)) heq
  rwa [completedRestriction_apply_of_mem (p j) Z z z.property hjZ,
    completedRestriction_apply_of_mem (p k) Z z z.property hkZ] at hval
end SoficGroups.MatchedComponentCompletion
