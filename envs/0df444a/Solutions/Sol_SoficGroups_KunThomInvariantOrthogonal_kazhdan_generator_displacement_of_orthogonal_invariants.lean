-- Prove2me | solution 1 for SoficGroups.KunThomInvariantOrthogonal.kazhdan_generator_displacement_of_orthogonal_invariants
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/4ad978da-b4a2-4bd9-96b9-6645e629ad93

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_kazhdan_generator_displacement
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_orthogonalRepresentation_no_fixed

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
    [CompleteSpace H] (P : SoficGroups.KazhdanPair.{u, v} G)
    (π : SoficGroups.UnitaryRepresentation G H) (x : H)
    (hx : x ≠ 0)
    (horth : ∀ y : H,
      (∀ g : G, π g y = y) → @inner ℂ H _ y x = 0) :
    ∃ g ∈ P.generators,
      P.kazhdanConstant * ‖x‖ ≤ ‖π g x - x‖ := by
  let z : (invariantSubmodule π)ᗮ :=
    ⟨x, (Submodule.mem_orthogonal _ _).mpr
      (fun y hy => horth y hy)⟩
  have hz : z ≠ 0 := by
    intro h
    apply hx
    exact congrArg Subtype.val h
  obtain ⟨g, hg, hgap⟩ :=
    SoficGroups.kazhdan_generator_displacement P
      (orthogonalRepresentation π)
      (orthogonalRepresentation_no_fixed π) z hz
  refine ⟨g, hg, ?_⟩
  simpa [z, orthogonalRepresentation, orthogonalLinearIsometryEquiv] using hgap
end SoficGroups.KunThomInvariantOrthogonal
