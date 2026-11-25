-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_TwoCases_intersectionNumber_baseChange_b63a01bf5c78
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:50:09.126175+00:00
-- url     : https://prove2.me/submissions/ac41b59a-bccb-4db4-b0a0-2679acd5a69a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_SumPderivRealApply
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TwoCasesDerivatives_sumPderivReal_apply_fbdf56144058
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TwoCasesDerivatives_sumPderivReal_X_300581b331cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TwoCasesDerivatives_deriv_restPoly_55a6298dcaea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
attribute [local simp] P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset TwoCasesDerivatives
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace TwoCases
theorem _root_.solution : IndefiniteRowSideFullHecke.RestTerms.TwoCases.Statement := by
  classical
  intro f j k I τ
  have hI : ∀ (c : ℝ) (P : IndefiniteRowSideFullHecke.RestTerms.Roots f j k), I (C c * P) = c * I P := by
    intro c P
    rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
  have hsh : ∀ F, IndefiniteRowSideFullHecke.RestTerms.shiftAt f j k I τ F =
      I (sumPderivReal f j k τ univ (Fin.castAdd k) F) := by
    intro F
    rw [sumPderivReal_apply]
    rfl
  have hto : ∀ F, IndefiniteRowSideFullHecke.RestTerms.totalAt f j k I τ F = I (sumPderivReal f j k τ univ id F) := by
    intro F
    rw [sumPderivReal_apply]
    rfl
  have shT : ∀ σ (a : Fin j), sumPderivReal f j k τ univ (Fin.castAdd k) (X (σ, Fin.castAdd k a)) =
      C (if σ = τ then 1 else 0) := by
    intro σ a
    rw [sumPderivReal_X]
    by_cases h : σ = τ <;> simp [h, Fin.castAdd_inj]
  have shB : ∀ σ (b : Fin k), sumPderivReal f j k τ univ (Fin.castAdd k) (X (σ, Fin.natAdd j b)) =
      C 0 := by
    intro σ b
    rw [sumPderivReal_X]
    refine (Finset.sum_eq_zero fun a _ => ?_).trans C_0.symm
    rw [if_neg]
    rintro ⟨-, h⟩
    have := congrArg Fin.val h
    simp at this
    omega
  have toX : ∀ σ i, sumPderivReal f j k τ univ id (X (σ, i)) = C (if σ = τ then 1 else 0) := by
    intro σ i
    rw [sumPderivReal_X]
    by_cases h : σ = τ <;> simp [h]
  have hs : ∑ σ : Fin f, (if σ = τ then (1 : ℝ) else 0) = 1 := by simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hsh, deriv_restPoly f j k _ true (fun σ => if σ = τ then 1 else 0) (fun _ => 0) shT shB,
      hI]
    simp
  · rw [hto, deriv_restPoly f j k _ true (fun σ => if σ = τ then 1 else 0)
      (fun σ => if σ = τ then 1 else 0) (fun σ a => toX σ _) (fun σ b => toX σ _), hI, if_pos rfl,
      hs]
    ring
  · rw [hsh, deriv_restPoly f j k _ false (fun σ => if σ = τ then 1 else 0) (fun _ => 0) shT shB,
      hI, if_neg Bool.false_ne_true, hs]
    ring
  · rw [hto, deriv_restPoly f j k _ false (fun σ => if σ = τ then 1 else 0)
      (fun σ => if σ = τ then 1 else 0) (fun σ a => toX σ _) (fun σ b => toX σ _), hI,
      if_neg Bool.false_ne_true, hs]
    ring
end TwoCases
end GroundTheory.Heights₂.Heights.RestTerms
