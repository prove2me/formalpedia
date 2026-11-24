-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchConcatExponent_proof_54a7cc4cf03f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:10:30.30616+00:00
-- url     : https://prove2.me/submissions/b47981c1-a141-47fb-a87f-9e23ce3657f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchConcatExponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchConcatExponent
theorem _root_.solution : SchConcatExponent.Statement := by
  intro r a c
  cases c with
  | first =>
    refine ⟨Equiv.refl _, fun lam hlam => ?_⟩
    funext p
    have hp := p.isLt
    by_cases h : (p : ℕ) < r
    · have := hlam ⟨p, h⟩
      simp [smallBlockOf, Schur.padPartition, h]
      omega
    · simp [smallBlockOf, Schur.padPartition, h]
      omega
  | last =>
    refine ⟨SchConcatExponent.rotate r a, fun lam hlam => ?_⟩
    funext p
    have hp := p.isLt
    simp only [Function.comp_apply]
    generalize hq : SchConcatExponent.rotate r a p = q
    have hv : (q : ℕ) = if (p : ℕ) < a then r + p else p - a := by
      rw [← hq]; exact SchConcatExponent.rotateFun_val r a p
    simp only [Schur.padPartition, smallBlockOf]
    by_cases h : (p : ℕ) < a
    · have hn : ¬ ((q : ℕ) < r) := by rw [hv, if_pos h]; omega
      rw [dif_pos h, dif_neg hn]
      simp only [Sum.elim_inr]
      rw [hv, if_pos h]
      omega
    · have h' : (p : ℕ) - a < r := by omega
      have hn : (q : ℕ) < r := by rw [hv, if_neg h]; exact h'
      rw [dif_neg h, dif_pos hn]
      simp only [Sum.elim_inl]
      have hqe : (⟨q, hn⟩ : Fin r) = ⟨(p : ℕ) - a, h'⟩ := Fin.ext (by rw [hv, if_neg h])
      rw [hqe, hv, if_neg h]
      have := hlam ⟨(p : ℕ) - a, h'⟩
      omega
end SchConcatExponent
end GroundTheory.Heights₂.Heights.RestTerms
