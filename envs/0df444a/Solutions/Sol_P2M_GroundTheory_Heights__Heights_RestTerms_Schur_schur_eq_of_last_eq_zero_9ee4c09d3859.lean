-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Schur_schur_eq_of_last_eq_zero_9ee4c09d3859
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:53:01.383288+00:00
-- url     : https://prove2.me/submissions/d37d5c60-97da-41d5-97de-aa8bc952d95d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Schur
open MvPolynomial Finset
noncomputable section
variable (σ : Type*) [Fintype σ] [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.RestTerms.Schur
theorem _root_.solution {n : ℕ} (lam : Fin (n + 1) → ℕ) (h : lam (Fin.last n) = 0) :
    schur σ lam = schur σ (fun i : Fin n => lam i.castSucc) := by
  unfold schur
  rw [Matrix.det_succ_row _ (Fin.last n)]
  rw [Fintype.sum_eq_single (Fin.last n)]
  · simp only [Matrix.of_apply, h, Fin.val_last, Fin.succAbove_last]
    rw [show ((0 : ℕ) : ℤ) - (n : ℤ) + (n : ℤ) = 0 by ring]
    simp [completeSymmetric, ← two_mul]
    rfl
  · intro j hj
    have hj' : (j : ℕ) < n := by
      have := j.isLt
      have : (j : ℕ) ≠ n := fun e => hj (Fin.ext e)
      omega
    simp only [Matrix.of_apply, h, Fin.val_last]
    rw [show completeSymmetric σ (((0 : ℕ) : ℤ) - (n : ℤ) + ((j : ℕ) : ℤ)) = 0 by
      unfold completeSymmetric; rw [if_neg (by omega)]]
    simp
end GroundTheory.Heights₂.Heights.RestTerms.Schur
