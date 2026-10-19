-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.representationFamilyMarkovLinear_subtype_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/3fc7b6e5-b10e-406b-9aaa-38690e5545ae

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedWordPower_representationFamilyMarkovLinear_subtype_apply

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v w
namespace SoficGroups.KunRootedWordPower
theorem _root_.solution
    {G H : Type*} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : SoficGroups.UnitaryRepresentation G H)
    (S : Finset G) (k : ℕ) (x : H) :
    (representationFamilyMarkovLinear π
        (fun i : ↥S => (i : G)) ^ k) x =
      ((unitaryFinsetMarkov π S)^[k]) x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply,
        Function.iterate_succ_apply', ih,
        representationFamilyMarkovLinear_subtype_apply]
end SoficGroups.KunRootedWordPower
