-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Section3_hypotheses_inhabited_6b2680fde2e6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:47.103851+00:00
-- url     : https://prove2.me/submissions/2e1f35ce-be80-44d9-ba4a-330fa8ba582b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements

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
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace Section3
theorem _root_.solution :
    4 * ((1 : ℕ) : ℝ) * (((1 + 1 : ℕ)) : ℝ) ^ 2 ≤ 16 ∧ (16 : ℝ) < 17 := by norm_num
end Section3
end GroundTheory.Heights₂.Heights.RestTerms
