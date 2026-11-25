-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_toFracModel_mem_e173d248237c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:22:38.283202+00:00
-- url     : https://prove2.me/submissions/ea37437b-2a13-4412-bb9d-4b3054cfab8b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalisationModelLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PNormalisationModelLocalizationX
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_toFrac_mem_05a26a7b558e

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
open GroundTheory.Heights₂.Heights.NormalisationModelLocalization
variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
variable (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
variable {M}
variable (M)
namespace GroundTheory.Heights₂.Heights.NormalisationModelLocalization
theorem _root_.solution (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (h : MvPolynomial (Fin n ⊕ Fin M.m) ℂ) :
    toFracModel M q h ∈ integralClosure (curveLocalRing J q) (FractionRing (curveLocalRing J q)) := by
  have hX : ∀ s, toFracModel M q (X s) ∈
      integralClosure (curveLocalRing J q) (FractionRing (curveLocalRing J q)) := by
    intro s
    cases s with
    | inl j =>
      rw [← rename_X (R := ℂ) (Sum.inl : Fin n → Fin n ⊕ Fin M.m) j, toFracModel_rename]
      exact toFrac_mem _
    | inr i =>
      obtain ⟨P, hPm, hP⟩ := M.integral i
      have h0 : toFracModel M q (P.eval₂ (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] _).toRingHom
          (X (Sum.inr i))) = 0 := by
        rw [← RingHom.mem_ker, ker_toFracModel hJ hq]
        exact hP
      rw [Polynomial.hom_eval₂] at h0
      have hc : (toFracModel M q).comp (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] _).toRingHom =
          (algebraMap (curveLocalRing J q) (FractionRing (curveLocalRing J q))).comp
            (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q)) :=
        RingHom.ext (toFracModel_rename M)
      rw [hc] at h0
      refine ⟨P.map (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q)), hPm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      exact h0
  induction h using MvPolynomial.induction_on with
  | C c =>
    rw [← rename_C (R := ℂ) (Sum.inl : Fin n → Fin n ⊕ Fin M.m) c, toFracModel_rename]
    exact toFrac_mem _
  | add p r hp hr =>
    rw [map_add]
    exact add_mem hp hr
  | mul_X p s hp =>
    rw [map_mul]
    exact mul_mem hp (hX s)
end GroundTheory.Heights₂.Heights.NormalisationModelLocalization
