-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_cutLevel_mem_6f1a40581949
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:11.302274+00:00
-- url     : https://prove2.me/submissions/79436eda-c3be-4b9f-84fb-cbd22675e896

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut

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
open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (k : ℕ) : 0 < cutLevel k ∧ cutLevel k < 1 := by
  refine ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (neg_neg_of_pos (Real.exp_pos _))⟩
end GroundTheory.Heights₂.Heights
