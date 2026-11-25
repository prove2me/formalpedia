-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_proof_3f97c41d1f77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:01:39.644819+00:00
-- url     : https://prove2.me/submissions/f5f95496-abdf-46c8-852d-bb054f31011d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalisationModelLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PNormalisationModelLocalizationX
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_algebraMap_e1ab69daa521
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_injective_a51db807acbc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_mem_35565d0006e6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_exists_locToFrac_33b3ccc2644e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_curveLocalRing_subsingleton_6e4911beb75a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mk_rename_mem_normalModelSubmonoid_b73a888102e6


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
open MvPolynomial ComplexSets
noncomputable section
open NormalisationModelLocalization
namespace GroundTheory.Heights₂.Heights
namespace NormalisationModelLocalization
theorem _root_.solution : NormalisationModelLocalization.Statement := by
  intro n J q M hJ
  by_cases hq : q ∈ zeroSet J
  · let g : Localization (normalModelSubmonoid M q) →+* curveNormalisation J q :=
      (locToFrac M hJ hq).codRestrict (integralClosure (curveLocalRing J q) (FractionRing (curveLocalRing J q)))
        (locToFrac_mem M hJ hq)
    have hbij : Function.Bijective g := by
      refine ⟨fun a b h => locToFrac_injective M hJ hq (congrArg Subtype.val h), ?_⟩
      rintro ⟨x, hx⟩
      obtain ⟨z, hz⟩ := exists_locToFrac M hJ hq x hx
      exact ⟨z, Subtype.ext hz⟩
    refine ⟨(RingEquiv.ofBijective g hbij).symm, fun f => ?_⟩
    rw [RingEquiv.symm_apply_eq]
    apply Subtype.ext
    change toFrac J q f = locToFrac M hJ hq (algebraMap _ _ (Ideal.Quotient.mk M.ideal (rename Sum.inl f)))
    rw [locToFrac_algebraMap, modelToFrac_mk, toFracModel_rename]
  · haveI := curveLocalRing_subsingleton J q hq
    haveI : Subsingleton (FractionRing (curveLocalRing J q)) :=
      IsLocalization.subsingleton (M := nonZeroDivisors (curveLocalRing J q))
        (by rw [Subsingleton.elim (0 : curveLocalRing J q) 1]; exact one_mem _)
    haveI : Subsingleton (curveNormalisation J q) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim (α := FractionRing (curveLocalRing J q)) _ _)⟩
    have h0 : (0 : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) ∈ normalModelSubmonoid M q := by
      simp only [zeroSet, Set.mem_ofPred_eq, not_forall] at hq
      obtain ⟨g, hg, hgq⟩ := hq
      have h1 := mk_rename_mem_normalModelSubmonoid M q g hgq
      rwa [Ideal.Quotient.eq_zero_iff_mem.2 ((rename_mem_iff M g).2 hg)] at h1
    haveI : Subsingleton (Localization (normalModelSubmonoid M q)) := IsLocalization.subsingleton h0
    let e : curveNormalisation J q ≃+* Localization (normalModelSubmonoid M q) :=
      { toFun := fun _ => 0
        invFun := fun _ => 0
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_add' := fun _ _ => Subsingleton.elim _ _ }
    exact ⟨e, fun _ => Subsingleton.elim _ _⟩
end NormalisationModelLocalization
end GroundTheory.Heights₂.Heights
