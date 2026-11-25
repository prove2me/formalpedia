-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_exists_coprime_mul_eq_zero_4a4cdbd8cee2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:41:37.704878+00:00
-- url     : https://prove2.me/submissions/df7c4def-01a0-4cbb-a9d6-e726b23cf57b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsLocSectionsInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PLocSectionsInj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_mul_eq_zero_of_pushout_inl_428d3945dc6e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry Opposite
noncomputable section
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : Nat.Primes) {V : X.Opens}
    (hV : IsAffineOpen V) (s : Γ(X, V)) (hs : (baseChangeMap f (ZLoc p)).app V s = 0) :
    ∃ u : ℤ, ¬ ((p : ℕ) : ℤ) ∣ u ∧ (u : Γ(X, V)) * s = 0 := by
  set φ : Spec (CommRingCat.of (ZLoc p)) ⟶ SpecZ := Spec.map (CommRingCat.ofHom (Int.castRingHom _))
  have H : IsPullback (pullback.fst f φ) (pullback.snd f φ) f φ := IsPullback.of_hasPullback f φ
  have hiso := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := V)
    (UY := pullback.fst f φ ⁻¹ᵁ V) le_top (by simp) (by simp) (isAffineOpen_top _)
    (isAffineOpen_top _) hV
  have h0 : pushout.inl (f.appLE ⊤ V (by simp)) (φ.appLE ⊤ ⊤ le_top) s = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (pushoutSection H (US := ⊤) (UT := ⊤) (UX := V)
      (UY := pullback.fst f φ ⁻¹ᵁ V) le_top _ _)).1
    rw [map_zero, ← CommRingCat.comp_apply, pushout.inl_desc, ← Scheme.Hom.app_eq_appLE]
    exact hs
  let eR : ℤ ≃+* Γ(SpecZ, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv.symm
  let eT : ZLoc p ≃+* Γ(Spec (CommRingCat.of (ZLoc p)), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (ZLoc p))).commRingCatIsoToRingEquiv.symm
  have key : (φ.appLE ⊤ ⊤ le_top).hom =
      eT.toRingHom.comp ((algebraMap ℤ (ZLoc p)).comp eR.symm.toRingHom) := by
    have h := RingHom.ext_int ((φ.appLE ⊤ ⊤ le_top).hom.comp eR.toRingHom)
      (eT.toRingHom.comp (algebraMap ℤ (ZLoc p)))
    ext x
    have h' := RingHom.congr_fun h (eR.symm x)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply] at h' ⊢
    exact h'
  have hT : @IsLocalization _ _ ((Ideal.span {((p : ℕ) : ℤ)}).primeCompl.map eR) _ _
      (φ.appLE ⊤ ⊤ le_top).hom.toAlgebra := by
    rw [key]
    let : Algebra Γ(SpecZ, ⊤) (ZLoc p) := ((algebraMap ℤ (ZLoc p)).comp eR.symm.toRingHom).toAlgebra
    have h1 : IsLocalization ((Ideal.span {((p : ℕ) : ℤ)}).primeCompl.map eR) (ZLoc p) :=
      IsLocalization.isLocalization_of_base_ringEquiv _ _ eR
    exact (IsLocalization.isLocalization_iff_of_ringEquiv _ eT).mp h1
  obtain ⟨m, hm, hma⟩ := exists_mul_eq_zero_of_pushout_inl _ _ _ hT s h0
  obtain ⟨u, hu, rfl⟩ := Submonoid.mem_map.mp hm
  refine ⟨u, fun h => hu (Ideal.mem_span_singleton.mpr h), ?_⟩
  rw [← hma]
  congr 1
  exact (map_intCast ((f.appLE ⊤ V (by simp)).hom.comp eR.toRingHom) u).symm
end GroundTheory.Heights₂.Heights.Model
