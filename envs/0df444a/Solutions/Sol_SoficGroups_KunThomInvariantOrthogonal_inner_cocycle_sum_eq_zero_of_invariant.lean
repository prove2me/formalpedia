-- Prove2me | solution 1 for SoficGroups.KunThomInvariantOrthogonal.inner_cocycle_sum_eq_zero_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/41e23f12-4f2e-46b2-b543-434e6eaf9adb

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_inner_cocycle_inv_of_invariant

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
    (S : Finset G) (hS : ∀ g ∈ S, g⁻¹ ∈ S)
    (y : H) (hy : ∀ g : G, π g y = y) :
    @inner ℂ H _ y (∑ g ∈ S, b g) = 0 := by
  classical
  rw [inner_sum]
  have hsymmetric : S⁻¹ = S := by
    ext g
    constructor
    · intro hg
      obtain ⟨a, ha, rfl⟩ := Finset.mem_inv.mp hg
      exact hS a ha
    · intro hg
      apply Finset.mem_inv.mpr
      exact ⟨g⁻¹, hS g hg, inv_inv g⟩
  have hneg :
      (∑ g ∈ S, @inner ℂ H _ y (b g)) =
        -(∑ g ∈ S, @inner ℂ H _ y (b g)) := by
    calc
      (∑ g ∈ S, @inner ℂ H _ y (b g)) =
          ∑ g ∈ S⁻¹, @inner ℂ H _ y (b g) := by rw [hsymmetric]
      _ = ∑ g ∈ S, @inner ℂ H _ y (b g⁻¹) :=
        Finset.sum_inv_index S (fun g => @inner ℂ H _ y (b g))
      _ = ∑ g ∈ S, -@inner ℂ H _ y (b g) := by
        apply Finset.sum_congr rfl
        intro g hg
        exact inner_cocycle_inv_of_invariant π b hb y hy g
      _ = -(∑ g ∈ S, @inner ℂ H _ y (b g)) := by
        rw [Finset.sum_neg_distrib]
  have hdouble :
      (2 : ℂ) * (∑ g ∈ S, @inner ℂ H _ y (b g)) = 0 := by
    calc
      (2 : ℂ) * (∑ g ∈ S, @inner ℂ H _ y (b g)) =
          (∑ g ∈ S, @inner ℂ H _ y (b g)) +
            (∑ g ∈ S, @inner ℂ H _ y (b g)) := two_mul _
      _ = (∑ g ∈ S, @inner ℂ H _ y (b g)) +
          -(∑ g ∈ S, @inner ℂ H _ y (b g)) :=
        congrArg (fun z : ℂ => (∑ g ∈ S, @inner ℂ H _ y (b g)) + z) hneg
      _ = 0 := add_neg_cancel _
  exact (mul_eq_zero.mp hdouble).resolve_left (by norm_num)
end SoficGroups.KunThomInvariantOrthogonal
