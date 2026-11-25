-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_finrank_gradedPiece_28c37d509f1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:26:25.666873+00:00
-- url     : https://prove2.me/submissions/cfd3a4c5-ee88-4d8f-b35a-4a8761b412fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinIntNum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_mul_pow_mem_map_iff_e06cc1491dc2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_homogSubmodule_eq_map_937d9ae32e0e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar pullDeg)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
theorem _root_.solution (V : Ideal (MRing ι F)) (M : K ⊕ Unit → ℕ) :
    Module.finrank F (gradedPiece (V.map (rename (liftVar (ι := ι) ptIdx))) M) =
      Module.finrank F (gradedPiece V (restrictFirst M)) := by
  set ψ := (LinearMap.mulRight F (X newVar ^ M (.inr ()))).comp
    (rename (liftVar (ι := ι) ptIdx)).toLinearMap with hψ
  set H := weightedHomogeneousSubmodule F (blockWeight ι) (restrictFirst M)
  set A := (Ideal.Quotient.mkₐ F (V.map (rename (liftVar (ι := ι) ptIdx)))).toLinearMap ∘ₗ ψ
  set B := (Ideal.Quotient.mkₐ F V).toLinearMap
  have hker : LinearMap.ker A = LinearMap.ker B := by
    ext f
    simp only [LinearMap.mem_ker, A, B, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hψ, LinearMap.mulRight_apply]
    exact mul_pow_mem_map_iff V f _
  have hA : gradedPiece (V.map (rename (liftVar (ι := ι) ptIdx))) M = H.map A := by
    unfold gradedPiece
    rw [homogSubmodule_eq_map, ← Submodule.map_comp]
  have hB : gradedPiece V (restrictFirst M) = H.map B := rfl
  have e : ∀ {N : Type} [AddCommGroup N] [Module F N] (C : MRing ι F →ₗ[F] N),
      H.map C = LinearMap.range (C ∘ₗ H.subtype) := by
    intro N _ _ C
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk2 : LinearMap.ker (A ∘ₗ H.subtype) = LinearMap.ker (B ∘ₗ H.subtype) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    rw [← LinearMap.mem_ker, hker, LinearMap.mem_ker]
  rw [hA, hB, e, e, ← (LinearMap.quotKerEquivRange _).finrank_eq,
    ← (LinearMap.quotKerEquivRange _).finrank_eq, hk2]
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
