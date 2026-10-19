-- Prove2me | solution 1 for SoficGroups.exists_permutation_embedding_of_expanding_centralizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/d53fb547-5819-4b71-8ac9-87f11e4eeeee

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_exists_finite_group_embedding_of_expanding_centralizer

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {G : Type*} [Group G] (F : Finset G)
    (M : ExpandingCentralizerFiniteModel G F) :
    ∃ (n : ℕ) (f : G → Equiv.Perm (Fin n)),
      Set.InjOn f (F : Set G) ∧ f 1 = 1 ∧
        ∀ x ∈ F, ∀ y ∈ F, f (x * y) = f x * f y := by
  obtain ⟨H, hgroup, hfinite, f, hinj, hone, hmul⟩ :=
    exists_finite_group_embedding_of_expanding_centralizer F M
  letI : Group H := hgroup
  letI : Finite H := hfinite
  letI : Fintype H := Fintype.ofFinite H
  let e : H ≃ Fin (Fintype.card H) := Fintype.equivFin H
  let ρ : H →* Equiv.Perm (Fin (Fintype.card H)) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom H H)
  have hρ : Function.Injective ρ :=
    e.permCongrHom.injective.comp MulAction.toPerm_injective
  refine ⟨Fintype.card H, fun x => ρ (f x), ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hinj hx hy (hρ hxy)
  · simp [hone]
  · intro x hx y hy
    change ρ (f (x * y)) = ρ (f x) * ρ (f y)
    rw [hmul x hx y hy, map_mul]
end SoficGroups
