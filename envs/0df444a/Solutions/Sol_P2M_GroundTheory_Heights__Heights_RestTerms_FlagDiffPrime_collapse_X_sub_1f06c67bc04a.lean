-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_collapse_X_sub_1f06c67bc04a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:44.7288+00:00
-- url     : https://prove2.me/submissions/0082e00e-280c-45a2-90fd-c0afa33f6502

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagDiffPrime

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
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.FlagDiffPrime
variable {σ : Type} [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.RestTerms.FlagDiffPrime
theorem _root_.solution (a b : σ) : collapse a b (X a - X b : MvPolynomial σ ℚ) = 0 := by
  simp [collapse]
end GroundTheory.Heights₂.Heights.RestTerms.FlagDiffPrime
