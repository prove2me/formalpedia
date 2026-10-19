-- Prove2me | solution 1 for SoficGroups.hasPropertyT_of_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/14f3ab2b-1610-481c-8ff2-7808f98918e5

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {G : Type u} {G' : Type w}
    [Group G] [Group G'] (e : G ≃* G')
    [HasPropertyT.{u, v} G] : HasPropertyT.{w, v} G' := by
  classical
  obtain ⟨P⟩ := HasPropertyT.exists_kazhdanPair (G := G)
  refine ⟨⟨{
    generators := P.generators.image e
    kazhdanConstant := P.kazhdanConstant
    positive := P.positive
    invariant := ?_
  }⟩⟩
  intro H _ _ _ π ξ hξ hξ'
  obtain ⟨η, hη, hη'⟩ := P.invariant H (π.comp e.toMonoidHom) ξ hξ (by
    intro g hg
    exact hξ' (e g) (Finset.mem_image.mpr ⟨g, hg, rfl⟩))
  refine ⟨η, hη, ?_⟩
  intro g
  obtain ⟨g, rfl⟩ := e.surjective g
  exact hη' g
end SoficGroups
