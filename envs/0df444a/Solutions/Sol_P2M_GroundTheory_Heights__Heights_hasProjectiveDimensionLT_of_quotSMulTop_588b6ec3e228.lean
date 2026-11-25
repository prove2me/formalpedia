-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLT_of_quotSMulTop_588b6ec3e228
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:34:23.403044+00:00
-- url     : https://prove2.me/submissions/156fce87-6ea3-49ac-96d0-18c5939c0c5a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AuslanderBuchsbaumDepthBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing CategoryTheory RingTheory.Sequence Ideal
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hxR : IsSMulRegular R x) (k : ℕ) (M : Type u) [AddCommGroup M]
    [Module R M] [Module.Finite R M] (hxM : IsSMulRegular M x)
    (hM : HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x M)) (k + 1)) :
    HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1) := by
  have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
  have : Nontrivial (R ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (R ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
  induction k generalizing M with
  | zero =>
    rw [zero_add, ← projective_iff_hasProjectiveDimensionLT_one, ← IsProjective.iff_projective]
      at hM ⊢
    have : Module.Finite (R ⧸ span {x}) (QuotSMulTop x M) :=
      Module.Finite.of_restrictScalars_finite R _ _
    have hfree : Module.Free (R ⧸ span {x}) (QuotSMulTop x M) := Module.free_of_flat_of_isLocalRing
    have := Module.finitePresentation_of_finite R M
    have : Module.Free R M :=
      (Module.free_quotSMulTop_iff_free R M (IsLocalRing.maximalIdeal_le_jacobson _ hx) hxM).mp hfree
    infer_instance
  | succ k ih =>
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    let K := LinearMap.ker π
    have hS := LinearMap.shortExact_shortComplexKer hπ
    have hproj : Projective (π.shortComplexKer).X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hxF : IsSMulRegular (Fin n → R) x := by
      intro a b h
      funext i
      exact hxR (congrFun h i)
    have hxK : IsSMulRegular K x := fun a b h ↦ Subtype.ext (hxF (congrArg Subtype.val h))
    let f₁ : QuotSMulTop x K →ₗ[R] QuotSMulTop x (Fin n → R) := QuotSMulTop.map x K.subtype
    let f₂ : QuotSMulTop x (Fin n → R) →ₗ[R] QuotSMulTop x M := QuotSMulTop.map x π
    have hex0 : Function.Exact K.subtype π := fun y ↦
      ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, by rintro ⟨k, rfl⟩; exact k.2⟩
    have ex : Function.Exact f₁ f₂ := QuotSMulTop.map_exact x hex0 hπ
    have surj : Function.Surjective f₂ := QuotSMulTop.map_surjective x hπ
    have inj : Function.Injective f₁ := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro y hy
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
      rw [LinearMap.mem_ker] at hy
      simp only [f₁, Submodule.mkQ_apply, QuotSMulTop.map_apply_mk, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_smul_pointwise_iff_exists] at hy
      obtain ⟨b, -, hb⟩ := hy
      have hπb : π b = 0 := by
        apply hxM
        show x • π b = x • 0
        rw [← map_smul, hb, smul_zero]
        exact y.2
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨⟨b, hπb⟩, Submodule.mem_top, Subtype.ext hb⟩
    let g₁ := f₁.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := span {x}))
    let g₂ := f₂.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := span {x}))
    let T := ModuleCat.shortComplexOfCompEqZero g₁ g₂
      (LinearMap.ext fun y ↦ ex.apply_apply_eq_zero y)
    have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T ex inj surj
    have hproj2 : Projective T.X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hK' : HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x K)) (k + 1) :=
      (hT.hasProjectiveDimensionLT_X₃_iff k hproj2).mp hM
    exact (hS.hasProjectiveDimensionLT_X₃_iff k hproj).mpr (ih K hxK hK')
end GroundTheory.Heights₂.Heights
