-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Elem_intWeight_nonneg_546dc8b33f2f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:41.3748+00:00
-- url     : https://prove2.me/submissions/f4c83350-4020-4fa9-bcdd-d43214de5254

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PrimeWeightEqZeroOfLt

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
open GroundTheory.Heights₂.Heights.RestTerms.Elem
namespace GroundTheory.Heights₂.Heights.RestTerms.Elem
theorem _root_.solution (B₀ : ℝ) (m : ℕ) : 0 ≤ intWeight B₀ m := by
  unfold intWeight
  split_ifs
  · exact div_nonneg (Real.log_natCast_nonneg m) (by positivity)
  · exact le_rfl
end GroundTheory.Heights₂.Heights.RestTerms.Elem
