-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FrobeniusCharacterFormula_proof_3a2a890a9856
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:05.735202+00:00
-- url     : https://prove2.me/submissions/d4de5a6c-0fb8-4575-80d2-104d61197009

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFrobeniusCharacterFormula
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_X_fin_ne_zero_ad271659adeb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_X_isHomogeneous_22912e03dba4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_psum_isHomogeneous_89f4e3dcb7ec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_isAlt_vandermonde_mul_prod_b74d8ff779cf


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
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FrobeniusCharacterFormula
theorem _root_.solution (h1 : SchAltPartitionExpansion.Statement) :
    FrobeniusCharacterFormula.Statement := by
  intro r q m _hq
  set V := vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) with hVdef
  set S := psum (Fin r) ℚ q * psum (Fin r) ℚ 1 ^ m with hSdef
  have hprod : ((q :: List.replicate m 1).map fun k => psum (Fin r) ℚ k).prod = S := by
    simp [S, List.map_replicate, List.prod_replicate]
  have halt : Comb.IsAlt (V * S) := by
    have := Comb.isAlt_vandermonde_mul_prod (m := r) (q :: List.replicate m 1)
    rwa [hprod] at this
  have hhom : (V * S).IsHomogeneous (r * (r - 1) / 2 + (q + m)) := by
    have h := (vandermondeOf_X_isHomogeneous r).mul
      ((psum_isHomogeneous (Fin r) q).mul ((psum_isHomogeneous (Fin r) 1).pow m))
    rwa [one_mul] at h
  have hexp := h1 r (q + m) (V * S) halt hhom
  apply mul_left_cancel₀ (vandermondeOf_X_fin_ne_zero r)
  rw [Finset.mul_sum]
  refine hexp.trans (Finset.sum_congr rfl fun lam _ => ?_)
  simp only [symmetricGroupCharacter, hprod]
  ring
end FrobeniusCharacterFormula
end GroundTheory.Heights₂.Heights.RestTerms
