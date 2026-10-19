-- Prove2me | solution 1 for SoficGroups.KunThomInvariantOrthogonal.inner_smul_cocycle_sum_eq_zero_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/0d541d38-9940-4acc-95a8-5999ea11ed34

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_inner_cocycle_sum_eq_zero_of_invariant

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
    (π : SoficGroups.UnitaryRepresentation G H) (b : G → H)
    (hb : ∀ g h : G, b (g * h) = b g + π g (b h))
    (S : Finset G) (hS : ∀ g ∈ S, g⁻¹ ∈ S) (c : ℂ)
    (y : H) (hy : ∀ g : G, π g y = y) :
    @inner ℂ H _ y (c • ∑ g ∈ S, b g) = 0 := by
  rw [inner_smul_right, inner_cocycle_sum_eq_zero_of_invariant π b hb S hS y hy,
    mul_zero]
end SoficGroups.KunThomInvariantOrthogonal
