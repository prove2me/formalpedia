-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CoordRatioDeg_proof_5e608c5ce409
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:09:04.919433+00:00
-- url     : https://prove2.me/submissions/010f4568-33dd-472f-afd7-28d7882df2d0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CoordRatioDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCoordRatioDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CoordRatioDeg_ratioField_map_a99e13e3712a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CoordRatioDeg_ratioField_congr_41a5f9c84a95
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Targets.CoordRatioDeg
namespace GroundTheory.Heights₂.Heights.Targets.CoordRatioDeg
theorem _root_.solution : CoordRatioDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v Ω _ _ y Φ' _ _ x' hv hker
  let I : Ideal (MRing ι') := mCoordIdeal y
  let L := FractionRing (MvPolynomial K' Ω)
  have : CharZero L := charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial K' Ω) L)
  have h₁ : ∀ a ∈ I, (aeval x' : MRing ι' →ₐ[ℤ] Φ').toRingHom a = 0 := fun a ha => by
    rw [show I = _ from hker.symm] at ha
    exact RingHom.mem_ker.mp ha
  have h₂ : ∀ a ∈ I, (mConeMap y).toRingHom a = 0 := fun a ha => RingHom.mem_ker.mp ha
  let g₁ : MRing ι' ⧸ I →+* Φ' := Ideal.Quotient.lift I _ h₁
  have hg₁ : Function.Injective g₁ :=
    RingHom.lift_injective_of_ker_le_ideal I h₁ fun a ha => by
      change a ∈ mCoordIdeal y
      rw [← hker]
      exact ha
  let g₂ : MRing ι' ⧸ I →+* L := (algebraMap _ L).comp (Ideal.Quotient.lift I _ h₂)
  have hg₂ : Function.Injective g₂ :=
    (IsFractionRing.injective _ L).comp (RingHom.lift_injective_of_ker_le_ideal I h₂ fun a ha => ha)
  have : IsDomain (MRing ι' ⧸ I) := hg₁.isDomain g₁
  let F := FractionRing (MRing ι' ⧸ I)
  let f₁ : F →+* Φ' := IsFractionRing.lift hg₁
  have : CharZero F := ⟨fun m n h => by
    have h' := congrArg f₁ h
    rw [map_natCast, map_natCast] at h'
    exact_mod_cast h'⟩
  let f₂ : F →+* L := IsFractionRing.lift hg₂
  let xb : (Σ k', ι' k') → F := fun p => algebraMap _ F (Ideal.Quotient.mk I (X p))
  have e₁ : f₁.toRatAlgHom ∘ xb = x' := funext fun p => by
    simp [xb, f₁, g₁, IsFractionRing.lift_algebraMap]
  have e₂ : ∀ p, f₂ (xb p) = algebraMap _ L (C (y p) * X p.1) := fun p => by
    simp [xb, f₂, g₂, IsFractionRing.lift_algebraMap, mConeMap]
  let c : Ω →ₐ[ℚ] L := ((algebraMap (MvPolynomial K' Ω) L).comp C).toRatAlgHom
  have hT : ∀ k, algebraMap (MvPolynomial K' Ω) L (X k) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).mpr (X_ne_zero k)
  have hr : ∀ p q : Σ k', ι' k', p.1 = q.1 → f₂ (xb p) / f₂ (xb q) = c (y p) / c (y q) := by
    intro p q h
    rw [e₂, e₂, h, map_mul, map_mul, mul_div_mul_right _ _ (hT _)]
    rfl
  change IntermediateField.relfinrank (ratioField (fun p q : Σ k, ι k => p.1 = q.1) (x' ∘ v))
      (ratioField (fun p q : Σ k', ι' k' => p.1 = q.1) x') =
    IntermediateField.relfinrank (ratioField (fun p q : Σ k, ι k => p.1 = q.1) (y ∘ v))
      (ratioField (fun p q : Σ k', ι' k' => p.1 = q.1) y)
  rw [← IntermediateField.relfinrank_map_map _ _ c, ratioField_map, ratioField_map, ← e₁,
    Function.comp_assoc, ← ratioField_map, ← ratioField_map,
    IntermediateField.relfinrank_map_map,
    ← IntermediateField.relfinrank_map_map _ _ f₂.toRatAlgHom, ratioField_map, ratioField_map]
  congr 1
  · refine ratioField_congr fun p q h => ?_
    simpa using hr (v p) (v q) (by rw [hv.2.2.1, hv.2.2.1, h])
  · exact ratioField_congr fun p q h => by simpa using hr p q h
end GroundTheory.Heights₂.Heights.Targets.CoordRatioDeg
