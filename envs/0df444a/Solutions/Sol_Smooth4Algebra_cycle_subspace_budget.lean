-- Prove2me | solution 1 for Smooth4Algebra.cycle_subspace_budget
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T06:00:59.423464+00:00
-- url     : https://prove2.me/submissions/769571e7-2b6c-4ba6-959f-8966694340e4

import Definitions.Def_Smooth4AlgebraHomology
import Mathlib.Tactic
set_option autoImplicit false

theorem solution
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W]
    (d : V →ₗ[K] V) (h_square : d.comp d = 0)
    (S : Submodule K V) (h_cycles : S ≤ LinearMap.ker d)
    (p : V →ₗ[K] W)
    (h_injective : Function.Injective
      (p.domRestrict (S ⊓ LinearMap.range d))) :
    Module.finrank K S - Module.finrank K (LinearMap.range (p.comp d)) ≤
      Module.finrank K (Smooth4Algebra.Homology d) := by
  have h_boundary : LinearMap.range d ≤ LinearMap.ker d := by
    rintro x ⟨y, rfl⟩
    have h := LinearMap.congr_fun h_square y
    simpa using h
  have h_dim_boundary :
      Module.finrank K (Smooth4Algebra.boundariesInCycles d) =
        Module.finrank K (LinearMap.range d) :=
    (Submodule.comapSubtypeEquivOfLe h_boundary).finrank_eq
  have h_homology := (Smooth4Algebra.boundariesInCycles d).finrank_quotient_add_finrank
  change Module.finrank K (Smooth4Algebra.Homology d) +
    Module.finrank K (Smooth4Algebra.boundariesInCycles d) =
    Module.finrank K (LinearMap.ker d) at h_homology
  rw [h_dim_boundary] at h_homology
  have h_sup : S ⊔ LinearMap.range d ≤ LinearMap.ker d :=
    sup_le h_cycles h_boundary
  have h_sup_dim := Submodule.finrank_mono h_sup
  have h_sum := S.finrank_sup_add_finrank_inf_eq (LinearMap.range d)
  let f : ↥(S ⊓ LinearMap.range d) →ₗ[K] LinearMap.range (p.comp d) :=
    (p.domRestrict (S ⊓ LinearMap.range d)).codRestrict
      (LinearMap.range (p.comp d)) (by
        intro x
        rcases x.property.2 with ⟨y, hy⟩
        exact ⟨y, by change p (d y) = p x; rw [hy]⟩)
  have h_f : Function.Injective f := by
    intro x y hxy
    apply h_injective
    exact congrArg Subtype.val hxy
  have h_inf_dim := LinearMap.finrank_le_finrank_of_injective h_f
  omega
