-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SmallRankWeakHypothesis_intersectionNumber_baseChange_46cb8718a615
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:51:09.751883+00:00
-- url     : https://prove2.me/submissions/c4f63de4-dcad-4c73-adcc-059bd7a00721

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary

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
open Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SmallRankWeakHypothesis
theorem _root_.solution : SmallRankWeakHypothesis.Statement := by
  intro h
  have := h 5 2 2 6 le_rfl (by norm_num) le_rfl (by norm_num)
  omega
end SmallRankWeakHypothesis
end GroundTheory.Heights₂.Heights.RestTerms
