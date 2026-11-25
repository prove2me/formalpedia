-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Schur_rename_completeSymmetric_4ab9f77ac719
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:52:32.136831+00:00
-- url     : https://prove2.me/submissions/6935728b-a864-4636-90f0-29f102cb0f21

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
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.RestTerms.Schur
theorem _root_.solution (e : Equiv.Perm σ) (d : ℤ) :
    rename e (completeSymmetric σ d) = completeSymmetric σ d := by
  unfold completeSymmetric
  split_ifs
  · exact hsymm_isSymmetric (σ := σ) (R := ℚ) _ e
  · simp
end GroundTheory.Heights₂.Heights.RestTerms.Schur
