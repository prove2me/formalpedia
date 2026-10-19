-- Prove2me | solution 1 for SoficGroups.KunThomInvariantOrthogonal.unitaryFinsetMarkov_orthogonal_invariants
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/c1f2ea78-78da-441d-af30-4eaa052d09f2

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
    (S : Finset G) (x : H)
    (horth : ∀ y : H,
      (∀ g : G, π g y = y) → @inner ℂ H _ y x = 0) :
    ∀ y : H, (∀ g : G, π g y = y) →
      @inner ℂ H _ y (unitaryFinsetMarkov π S x) = 0 := by
  have hx : x ∈ (invariantSubmodule π)ᗮ :=
    (Submodule.mem_orthogonal _ _).mpr (fun y hy => horth y hy)
  have hsum : (∑ g ∈ S, π g x) ∈ (invariantSubmodule π)ᗮ := by
    apply Submodule.sum_mem
    intro g hg
    exact map_mem_invariantSubmodule_orthogonal π g hx
  have hmarkov :
      unitaryFinsetMarkov π S x ∈ (invariantSubmodule π)ᗮ := by
    exact (invariantSubmodule π)ᗮ.smul_mem _ hsum
  intro y hy
  exact (Submodule.mem_orthogonal _ _).mp hmarkov y hy
end SoficGroups.KunThomInvariantOrthogonal
