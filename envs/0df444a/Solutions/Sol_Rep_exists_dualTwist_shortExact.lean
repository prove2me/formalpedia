-- Prove2me | solution 1 for Rep.exists_dualTwist_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/945314e3-1c77-5794-b508-cb3f9d5ee7e3

import Mathlib
import Definitions.Def_GroupCohomology_Selmer
import Theorems.Thm_LinearMap_exact_dualMap_of_exact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exists_dualTwist_shortExact

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

open CategoryTheory

theorem solution {k G : Type u} [Field k] [Group G] (χ : G →* kˣ)
    {M' M M'' : Rep.{u} k G} (i : M' ⟶ M) (π : M ⟶ M'')
    (hi : Function.Injective i.hom) (hπ : Function.Surjective π.hom)
    (hex : ∀ m : M, π.hom m = 0 ↔ ∃ m' : M', i.hom m' = m) :
    ∃ (πD : M''.dualTwist χ ⟶ M.dualTwist χ) (iD : M.dualTwist χ ⟶ M'.dualTwist χ),
      (∀ (f : M''.dualTwist χ) (m : M), (πD.hom f : Module.Dual k M) m = (f : Module.Dual k M'') (π.hom m)) ∧
      (∀ (f : M.dualTwist χ) (m' : M'), (iD.hom f : Module.Dual k M') m' = (f : Module.Dual k M) (i.hom m')) ∧
      Function.Injective πD.hom ∧ Function.Surjective iD.hom ∧
      (∀ f : M.dualTwist χ, iD.hom f = 0 ↔ ∃ f'' : M''.dualTwist χ, πD.hom f'' = f) := by
  classical

  have hdual : ∀ {A B : Rep.{u} k G} (ψ : A ⟶ B) (g : G) (f : B.dualTwist χ),
      (ψ.hom.toLinearMap.dualMap) ((B.dualTwist χ).ρ g f) = (A.dualTwist χ).ρ g (ψ.hom.toLinearMap.dualMap f) := by
    intro A B ψ g f
    apply LinearMap.ext; intro a
    rw [LinearMap.dualMap_apply, Rep.dualTwist_ρ_apply, Rep.dualTwist_ρ_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.dualMap_apply]
    congr 2
    exact (Rep.hom_comm_apply ψ g⁻¹ a).symm
  let D : ∀ {A B : Rep.{u} k G} (ψ : A ⟶ B), B.dualTwist χ ⟶ A.dualTwist χ := fun {A B} ψ =>
    Rep.ofHom (ψ.hom.toLinearMap.dualMap.intertwiningMap_of_isIntertwiningMap (B.dualTwist χ).ρ (A.dualTwist χ).ρ
      (fun g f => hdual ψ g f))
  have hD : ∀ {A B : Rep.{u} k G} (ψ : A ⟶ B) (f : B.dualTwist χ), (D ψ).hom f = ψ.hom.toLinearMap.dualMap f :=
    fun _ _ => rfl
  refine ⟨D π, D i, fun f m => rfl, fun f m' => rfl, ?_, ?_, ?_⟩
  ·
    intro f f' h
    have h' : π.hom.toLinearMap.dualMap f = π.hom.toLinearMap.dualMap f' := h
    exact LinearMap.dualMap_injective_of_surjective hπ h'
  ·
    intro f'
    obtain ⟨f, hf⟩ := LinearMap.dualMap_surjective_of_injective (f := i.hom.toLinearMap) hi f'
    exact ⟨f, hf⟩
  ·
    intro f
    have hexact : Function.Exact i.hom.toLinearMap π.hom.toLinearMap := fun m =>
      ⟨fun h => by obtain ⟨m', hm'⟩ := (hex m).1 h; exact ⟨m', hm'⟩, fun ⟨m', hm'⟩ => (hex m).2 ⟨m', hm'⟩⟩
    have := LinearMap.exact_dualMap_of_exact _ _ hexact f
    exact this

end S_Rep_exists_dualTwist_shortExact
end P2MW
export P2MW.S_Rep_exists_dualTwist_shortExact (solution)
