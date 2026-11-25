-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_schur_rowOne_94c2ce3effa1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:11:50.567826+00:00
-- url     : https://prove2.me/submissions/5a47e310-971a-46e6-8580-7d340e4e2448

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PLinearTermValue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_completeSymmetric_neg_9ceb165058bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_completeSymmetric_zero_8b38a07da8f0


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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (σ : Type*) [Fintype σ] [DecidableEq σ] (r : ℕ) (hr : 1 ≤ r) :
    schur σ (rowOne r) = ∑ i : σ, X i := by
  unfold schur
  rw [Matrix.det_of_isUpperTriangular]
  · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [Fin.prod_univ_succ]
    have h1 : ∏ i : Fin r', Matrix.of (fun i j : Fin (r' + 1) =>
        completeSymmetric σ ((rowOne (r' + 1) i : ℤ) - ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ)))
        i.succ i.succ = 1 :=
      Finset.prod_eq_one fun i _ => by simp [rowOne, completeSymmetric_zero]
    rw [h1, mul_one]
    simp [rowOne, completeSymmetric, hsymm_one]
  · intro i j hij
    simp only [Matrix.of_apply]
    apply completeSymmetric_neg
    have : (j : ℕ) < i := hij
    simp only [rowOne]
    split_ifs with h
    · omega
    · push_cast; omega
end GroundTheory.Heights₂.Heights.RestTerms.Top
