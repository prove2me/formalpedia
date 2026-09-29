-- Prove2me | solution 1 for Rep.shortExact_map_tensorLeft_of_splitting
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4745563c-f308-551e-8f93-c36deb8b034e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_shortExact_map_tensorLeft_of_splitting

set_option autoImplicit false
universe u
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory"

namespace P2mS26SplitL

variable {k G : Type u} [CommRing k] [Group G]

theorem exists_retraction {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
    (s : X.X₃ →ₗ[k] X.X₂) (hs : ∀ x : X.X₃, X.g.hom (s x) = x) :
    ∃ r : X.X₂ →ₗ[k] X.X₁, r ∘ₗ X.f.hom.toLinearMap = LinearMap.id := by
  have hinj : Function.Injective X.f.hom.toLinearMap := (Rep.mono_iff_injective X.f).1 hX.mono_f
  have hker : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
    (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  let φ : X.X₂ →ₗ[k] X.X₂ := LinearMap.id - s ∘ₗ X.g.hom.toLinearMap
  have hmem : ∀ y, φ y ∈ LinearMap.range X.f.hom.toLinearMap := fun y => by
    rw [hker, LinearMap.mem_ker]
    show X.g.hom (y - s (X.g.hom y)) = 0
    rw [map_sub, hs, sub_self]
  refine ⟨(LinearEquiv.ofInjective _ hinj).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range X.f.hom.toLinearMap) φ hmem, ?_⟩
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply]
  apply (LinearEquiv.ofInjective _ hinj).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [LinearEquiv.ofInjective_apply, LinearMap.codRestrict_apply]
  show X.f.hom x - s (X.g.hom (X.f.hom x)) = X.f.hom x
  have h0 : X.g.hom (X.f.hom x) = 0 := by
    show X.f.hom.toLinearMap x ∈ LinearMap.ker X.g.hom.toLinearMap
    rw [← hker]
    exact ⟨x, rfl⟩
  rw [h0, map_zero, sub_zero]

end P2mS26SplitL

open P2mS26SplitL in
theorem solution {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
    (s : X.X₃ →ₗ[k] X.X₂) (hs : ∀ x : X.X₃, X.g.hom (s x) = x) (A : Rep.{u} k G) :
    (X.map (MonoidalCategory.tensorLeft A)).ShortExact := by
  have hsurj : Function.Surjective X.g.hom.toLinearMap := (Rep.epi_iff_surjective X.g).1 hX.epi_g
  have hker : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
    (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  have hexact : Function.Exact X.f.hom.toLinearMap X.g.hom.toLinearMap := LinearMap.exact_iff.2 hker.symm
  obtain ⟨r, hr⟩ := exists_retraction hX s hs
  have hT : Function.Exact (X.f.hom.toLinearMap.lTensor A) (X.g.hom.toLinearMap.lTensor A) :=
    lTensor_exact A hexact hsurj
  exact
    { exact := (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful _
        ((ShortComplex.moduleCat_exact_iff _).2 fun y hy => by
          obtain ⟨x, hx⟩ := (hT y).1 hy
          exact ⟨x, hx⟩)
      mono_f := (Rep.mono_iff_injective _).2 (by
        change Function.Injective (X.f.hom.toLinearMap.lTensor A)
        refine Function.LeftInverse.injective (g := r.lTensor A) fun t => ?_
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hr, LinearMap.lTensor_id, LinearMap.id_apply])
      epi_g := (Rep.epi_iff_surjective _).2 (by
        change Function.Surjective (X.g.hom.toLinearMap.lTensor A)
        exact LinearMap.lTensor_surjective _ hsurj) }

end S_Rep_shortExact_map_tensorLeft_of_splitting
end P2MW
export P2MW.S_Rep_shortExact_map_tensorLeft_of_splitting (solution)
