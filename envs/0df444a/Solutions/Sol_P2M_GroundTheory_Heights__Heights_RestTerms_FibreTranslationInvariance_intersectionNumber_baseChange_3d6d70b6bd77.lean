-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FibreTranslationInvariance_intersectionNumber_baseChange_3d6d70b6bd77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:53:39.772862+00:00
-- url     : https://prove2.me/submissions/ce5fe14f-b434-4778-b3f0-2a21bfcc3d6c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_apply_de6d8a815ba9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_X_8d74257f5c74
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_yIndex_eq_yIndex_iff_2a9541f0912b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_zIndex_eq_zIndex_iff_16e9951ee638
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_yIndex_ne_zIndex_0cbfe6a22674
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_derivation_restPolynomial_b9129232db91

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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FibreTranslationInvariance
theorem _root_.solution : FibreTranslationInvariance.Statement := by
  classical
  intro f r a c τ
  constructor
  · have h := (Flag.derivation_restPolynomial f r a c
      (Flag.sumPderiv Finset.univ (yIndex f r a c τ)) (fun σ => if σ = τ then 1 else 0) (fun _ => 0)
      (fun σ i => by
        rw [Flag.sumPderiv_X]
        by_cases h : σ = τ
        · subst h
          rw [show (Finset.univ.filter fun l => yIndex f r a c σ l = yIndex f r a c σ i) = {i} by
            ext l; simp [Flag.yIndex_eq_yIndex_iff]]
          simp
        · rw [show (Finset.univ.filter fun l => yIndex f r a c τ l = yIndex f r a c σ i) = ∅ by
            ext l; simp [Flag.yIndex_eq_yIndex_iff, Ne.symm h]]
          simp [h])
      (fun σ i => by
        rw [Flag.sumPderiv_X]
        rw [show (Finset.univ.filter fun l => yIndex f r a c τ l = zIndex f r a c σ i) = ∅ by
          ext l; simp [Flag.yIndex_ne_zIndex]]
        simp)).1
    rw [Flag.sumPderiv_apply] at h
    exact h
  · have h := (Flag.derivation_restPolynomial f r a c
      (Flag.sumPderiv Finset.univ (zIndex f r a c τ)) (fun _ => 0) (fun σ => if σ = τ then 1 else 0)
      (fun σ i => by
        rw [Flag.sumPderiv_X]
        rw [show (Finset.univ.filter fun l => zIndex f r a c τ l = yIndex f r a c σ i) = ∅ by
          ext l
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          exact fun h => Flag.yIndex_ne_zIndex c σ τ i l h.symm]
        simp)
      (fun σ i => by
        rw [Flag.sumPderiv_X]
        by_cases h : σ = τ
        · subst h
          rw [show (Finset.univ.filter fun l => zIndex f r a c σ l = zIndex f r a c σ i) = {i} by
            ext l; simp [Flag.zIndex_eq_zIndex_iff]]
          simp
        · rw [show (Finset.univ.filter fun l => zIndex f r a c τ l = zIndex f r a c σ i) = ∅ by
            ext l; simp [Flag.zIndex_eq_zIndex_iff, Ne.symm h]]
          simp [h])).1
    rw [Flag.sumPderiv_apply] at h
    exact h
end FibreTranslationInvariance
end GroundTheory.Heights₂.Heights.RestTerms
