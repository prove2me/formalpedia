-- Prove2me | solution 1 for SoficGroups.KunThomInvariantOrthogonal.orthogonalRepresentation_no_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/7512c0cd-199b-4520-adde-03833052ca10

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomInvariantOrthogonal
open Filter Topology
open scoped ComplexConjugate Pointwise
universe u v
variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace SoficGroups.KunThomInvariantOrthogonal
theorem _root_.solution
    (π : SoficGroups.UnitaryRepresentation G H)
    (x : (invariantSubmodule π)ᗮ)
    (hx : ∀ g : G, orthogonalRepresentation π g x = x) :
    x = 0 := by
  have hxinv : (x : H) ∈ invariantSubmodule π := by
    intro g
    exact congrArg Subtype.val (hx g)
  have hinner : @inner ℂ H _ (x : H) (x : H) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hxinv x.property
  apply Subtype.ext
  change (x : H) = 0
  exact inner_self_eq_zero.mp hinner
end SoficGroups.KunThomInvariantOrthogonal
