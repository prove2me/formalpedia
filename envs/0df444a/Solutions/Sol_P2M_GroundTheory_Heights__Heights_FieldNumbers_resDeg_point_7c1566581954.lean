-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_resDeg_point_7c1566581954
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:55:24.140098+00:00
-- url     : https://prove2.me/submissions/4b34bf07-bc3d-44e5-a99a-a8c7a72a6165

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_eq_monomial_of_isMultiHomog_point_043f9fbc675f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (F : Type*) [Field F] : resDeg (⊥ : Ideal (MRing (ProjIdx 0) F)) = 1 := by
  unfold resDeg
  rw [dif_pos Ideal.isPrime_bot]
  have hle : homFracDegZero (⊥ : Ideal (MRing (ProjIdx 0) F)) = ⊥ := by
    refine le_antisymm ?_ bot_le
    unfold homFracDegZero
    rw [IntermediateField.adjoin_le_iff]
    rintro x ⟨b, f, g, hf, hg, hgP, rfl⟩
    rw [SetLike.mem_coe, IntermediateField.mem_bot]
    have ef := eq_monomial_of_isMultiHomog_point f b hf
    have eg := eq_monomial_of_isMultiHomog_point g b hg
    rw [← C_mul_X_pow_eq_monomial] at ef eg
    generalize coeff (Finsupp.single ⟨(), 0⟩ (b ())) f = a at ef
    generalize coeff (Finsupp.single ⟨(), 0⟩ (b ())) g = c at eg
    generalize b () = n at ef eg
    set v : (Σ _ : Unit, ProjIdx 0 ()) := ⟨(), 0⟩
    have hc : c ≠ 0 := by
      rintro rfl
      apply hgP
      rw [eg, C_0, zero_mul]
      exact Ideal.zero_mem _
    have hY : algebraMap (MRing (ProjIdx 0) F ⧸ (⊥ : Ideal (MRing (ProjIdx 0) F)))
        (FractionRing (MRing (ProjIdx 0) F ⧸ (⊥ : Ideal (MRing (ProjIdx 0) F))))
        (Ideal.Quotient.mk _ (X v ^ n)) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_bot]
      exact pow_ne_zero _ (X_ne_zero _)
    refine ⟨a / c, ?_⟩
    rw [ef, eg, map_mul, map_mul, map_mul, map_mul, ← MvPolynomial.algebraMap_eq,
      Ideal.Quotient.mk_algebraMap, Ideal.Quotient.mk_algebraMap,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      mul_div_mul_right _ _ hY, map_div₀]
  rw [hle, IntermediateField.finrank_bot]
end GroundTheory.Heights₂.Heights.FieldNumbers
