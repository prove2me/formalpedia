-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Schur_completeSymmetric_natSub_050630c5ac60
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:45.387358+00:00
-- url     : https://prove2.me/submissions/fff0aa7e-0052-4c09-95fb-ae9ad3dfbafd

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
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Schur
theorem _root_.solution (σ : Type*) [Fintype σ] [DecidableEq σ] (a c : ℕ) :
    completeSymmetric σ ((a : ℤ) - (c : ℤ)) = if c ≤ a then hsymm σ ℚ (a - c) else 0 := by
  unfold completeSymmetric
  split_ifs with h1 h2 h2
  · congr 1; omega
  · omega
  · omega
  · rfl
end GroundTheory.Heights₂.Heights.RestTerms.Schur
