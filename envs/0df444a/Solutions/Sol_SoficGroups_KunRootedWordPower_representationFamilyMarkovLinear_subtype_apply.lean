-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.representationFamilyMarkovLinear_subtype_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/b8e7dda3-cc98-49a2-aa37-8e7c45258bea

import Mathlib
import Definitions.Def_NonSoficGroup

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
    (S : Finset G) (x : H) :
    representationFamilyMarkovLinear π (fun i : ↥S => (i : G)) x =
      unitaryFinsetMarkov π S x := by
  simp [representationFamilyMarkovLinear, unitaryFinsetMarkov,
    ← Finset.sum_coe_sort S]
end SoficGroups.KunRootedWordPower
