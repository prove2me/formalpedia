-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SmallRankBound_hypotheses_inhabited_4ec382f0f031
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:47.867436+00:00
-- url     : https://prove2.me/submissions/0760a8d3-8d08-41cb-aaa0-d43f5ff137bd

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
namespace SmallRankBound
theorem _root_.solution :
    2 ≤ 2 ∧ 2 ^ 4 ≤ 16 ∧ 2 ≤ 2 ∧ 17 = 16 + 2 - 1 := by decide
end SmallRankBound
end GroundTheory.Heights₂.Heights.RestTerms
