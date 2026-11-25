-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Schur_schur_padPartition_94764fcf450d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:57:08.585854+00:00
-- url     : https://prove2.me/submissions/38e9359f-7100-4d7e-8ade-256e39ae0b06

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_schur_eq_of_last_eq_zero_9ee4c09d3859

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
theorem _root_.solution {r : ℕ} (lam : Fin r → ℕ) :
    ∀ n : ℕ, r ≤ n → schur σ (padPartition n lam) = schur σ lam := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    congr 1
    funext i
    simp [padPartition]
  | succ n hrn ih =>
    rw [schur_eq_of_last_eq_zero]
    · rw [← ih]
      congr 1
    · simp [padPartition]
      omega
end GroundTheory.Heights₂.Heights.RestTerms.Schur
