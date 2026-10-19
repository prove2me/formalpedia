-- Prove2me | solution 1 for SoficGroups.MatchedComponentCompletion.completedRestriction_commute_of_not_mem_sourceCompletionBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/64f0ef73-c193-49cc-b4fe-429fe3dedef1

import Mathlib
import Definitions.Def_NonSoficGroup
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
    (σZ : ι → Equiv.Perm {x : V // x ∈ Z})
    (hσZ : ∀ i (x : V) (hx : x ∈ Z) (_hi : σ i x ∈ Z),
      ((σZ i ⟨x, hx⟩ : {x : V // x ∈ Z}) : V) = σ i x)
    {j : J}
    (hj : j ∈ SoficGroups.CompressionCriterion.productTrackedTable F)
    (i : ι) (z : {x : V // x ∈ Z})
    (hz : (z : V) ∉ sourceCompletionBad σ p F Z) :
    completedRestriction (p j) Z (σZ i z) =
      σZ i (completedRestriction (p j) Z z) := by
  have hg := sourceCompletionBad_good σ p F Z z z.property hz
  have hσmem : σ i (z : V) ∈ Z := hg.1 i
  have hjmem : p j (z : V) ∈ Z := hg.2.1 j hj
  have hcomm : p j (σ i (z : V)) = σ i (p j (z : V)) :=
    hg.2.2.1 i j hj
  have hcomposite : p j (σ i (z : V)) ∈ Z :=
    hg.2.2.2.1 i j hj
  have hσvalue :
      ((σZ i z : {x : V // x ∈ Z}) : V) = σ i (z : V) :=
    hσZ i z z.property hσmem
  have hjvalue :
      ((completedRestriction (p j) Z z : {x : V // x ∈ Z}) : V) =
        p j (z : V) :=
    completedRestriction_apply_of_mem (p j) Z z z.property hjmem
  have hleftmem : p j ((σZ i z : {x : V // x ∈ Z}) : V) ∈ Z := by
    rw [hσvalue]
    exact hcomposite
  have hrightmem :
      σ i
        ((completedRestriction (p j) Z z : {x : V // x ∈ Z}) : V) ∈ Z := by
    rw [hjvalue, ← hcomm]
    exact hcomposite
  apply Subtype.ext
  calc
    ((completedRestriction (p j) Z (σZ i z) :
        {x : V // x ∈ Z}) : V) =
        p j ((σZ i z : {x : V // x ∈ Z}) : V) :=
      completedRestriction_apply_of_mem
        (p j) Z (σZ i z) (σZ i z).property hleftmem
    _ = p j (σ i (z : V)) := congrArg (p j) hσvalue
    _ = σ i (p j (z : V)) := hcomm
    _ = σ i
        ((completedRestriction (p j) Z z : {x : V // x ∈ Z}) : V) :=
      congrArg (σ i) hjvalue.symm
    _ = ((σZ i (completedRestriction (p j) Z z) :
        {x : V // x ∈ Z}) : V) :=
      (hσZ i (completedRestriction (p j) Z z)
        (completedRestriction (p j) Z z).property hrightmem).symm
end SoficGroups.MatchedComponentCompletion
