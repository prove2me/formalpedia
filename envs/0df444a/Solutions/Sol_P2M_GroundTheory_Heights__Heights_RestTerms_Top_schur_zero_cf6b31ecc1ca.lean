-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_schur_zero_cf6b31ecc1ca
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:41.052275+00:00
-- url     : https://prove2.me/submissions/401e561e-560b-498d-a146-c425b2ad0d58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_completeSymmetric_zero_8b38a07da8f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_completeSymmetric_neg_9ceb165058bd

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
theorem _root_.solution (σ : Type*) [Fintype σ] [DecidableEq σ] (m : ℕ) :
    schur σ (0 : Fin m → ℕ) = 1 := by
  unfold schur
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [completeSymmetric_zero]
  · intro i j hij
    simp only [Matrix.of_apply, Pi.zero_apply, Nat.cast_zero, zero_sub]
    apply completeSymmetric_neg
    have : (j : ℕ) < i := hij
    omega
end GroundTheory.Heights₂.Heights.RestTerms.Top
