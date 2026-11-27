-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_ZLocDenominators_proof_4beb967a4c3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:04:59.600171+00:00
-- url     : https://prove2.me/submissions/09dcc2d5-fa2b-4d38-a683-1ec586f9b3a9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsZLocDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PZLocDenominators
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_of_iso_15fe1f0a6e57
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsVectorBundle_of_iso_efcac834adba


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
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.ZLocDenominators
namespace GroundTheory.Heights₂.Heights.Model.ZLocDenominators
theorem _root_.solution : ZLocDenominators.Statement := by
  intro X f p U hU
  have : IsAffineHom (baseChangeMap f (ZLoc p)) := by
    set_option backward.isDefEq.respectTransparency.types false in
    exact MorphismProperty.pullback_fst _ _ inferInstance
  set g := baseChangeMap f (ZLoc p) with hg
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  intro b
  let φ : Γ(X, U) ⟶ Γ(baseChange f (ZLoc p), g ⁻¹ᵁ U) := g.appLE U (g ⁻¹ᵁ U) le_rfl
  have hφ : g.app U = φ := Scheme.Hom.app_eq_appLE _
  let ιA : CommRingCat.of ℤ ⟶ Γ(X, U) := CommRingCat.ofHom (Int.castRingHom Γ(X, U))
  let h : CommRingCat.of ℤ ⟶ CommRingCat.of (ZLoc p) :=
    CommRingCat.ofHom (Int.castRingHom (ZLoc p))
  have hUf : hU.fromSpec ≫ f = Spec.map ιA := specZIsTerminal.hom_ext _ _

  have key := IsAffineOpen.SpecMap_appLE_fromSpec g hU hV le_rfl
  have Pgeo : IsPullback (Spec.map φ) (hV.fromSpec ≫ pullback.snd f (Spec.map h))
      (Spec.map ιA) (Spec.map h) := by
    have P := (isPullback_morphismRestrict g U).paste_vert (IsPullback.of_hasPullback f (Spec.map h))
    rw [← hUf]
    refine P.of_iso hV.isoSpec hU.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [← cancel_mono hU.fromSpec, Category.assoc, Category.assoc, key, ← hU.isoSpec_inv_ι,
        ← hV.isoSpec_inv_ι]
      simp [morphismRestrict_ι]
    · rw [← hV.isoSpec_inv_ι]
      simp
    · rw [← hU.isoSpec_inv_ι]
      simp
    · simp

  let S : Submonoid ℤ := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl
  let M : Submonoid Γ(X, U) := S.map (Int.castRingHom Γ(X, U))
  let L := Localization M
  let fZ : ZLoc p →+* L := IsLocalization.map (M := S) (S := ZLoc p) L
    (Int.castRingHom Γ(X, U)) (T := M) (Submonoid.le_comap_map _)
  have H : fZ.comp (algebraMap ℤ (ZLoc p)) = (algebraMap Γ(X, U) L).comp (Int.castRingHom Γ(X, U)) :=
    IsLocalization.map_comp _
  have Palg := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (Int.castRingHom Γ(X, U)) fZ H S)
  have hh : algebraMap ℤ (ZLoc p) = Int.castRingHom (ZLoc p) := Subsingleton.elim _ _
  rw [hh] at Palg
  let e := Pgeo.isoIsPullback _ _ Palg
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective e.hom
  obtain ⟨χ, hχ⟩ := Spec.map_surjective e.inv
  have hcomp : CommRingCat.ofHom (algebraMap Γ(X, U) L) ≫ ψ = φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ]
    exact IsPullback.isoIsPullback_hom_fst _ _ Pgeo Palg
  have hχψ : χ ≫ ψ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hχ, Iso.hom_inv_id, Spec.map_id]
  have hφa : ∀ a, φ a = ψ (algebraMap Γ(X, U) L a) := fun a => by rw [← hcomp]; rfl
  have hψa : ∀ b, ψ (χ b) = b := fun b => by
    rw [← CommRingCat.comp_apply, hχψ]; rfl

  obtain ⟨⟨a, m⟩, ham⟩ := IsLocalization.surj M (χ b)
  obtain ⟨n, hn, hnm⟩ := Submonoid.mem_map.mp m.2
  have hpn : ¬ ((p : ℕ) : ℤ) ∣ n := fun hd => hn (Ideal.mem_span_singleton.mpr hd)
  have hn0 : n ≠ 0 := by rintro rfl; exact hpn (dvd_zero _)
  have hb : b * (n : Γ(baseChange f (ZLoc p), g ⁻¹ᵁ U)) = φ a := by
    have := congrArg ψ ham
    rw [map_mul, hψa, ← hφa, ← hφa, ← hnm] at this
    simpa using this
  refine ⟨n.natAbs, Int.natAbs_pos.mpr hn0, fun hd => hpn (Int.natCast_dvd.mpr hd), ?_⟩
  rw [hφ, nsmul_eq_mul]
  rcases Int.natAbs_eq n with hn' | hn'
  · refine ⟨a, ?_⟩
    rw [← hb, mul_comm, hn']
    simp
  · refine ⟨-a, ?_⟩
    rw [map_neg, ← hb, mul_comm, hn']
    simp
end GroundTheory.Heights₂.Heights.Model.ZLocDenominators
