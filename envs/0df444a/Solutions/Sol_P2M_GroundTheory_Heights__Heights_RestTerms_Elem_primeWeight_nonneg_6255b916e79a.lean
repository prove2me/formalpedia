-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Elem_primeWeight_nonneg_6255b916e79a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:08.456842+00:00
-- url     : https://prove2.me/submissions/4f0d7c6f-b447-4072-9551-9fe934f65431

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
theorem _root_.solution (B : ℝ) (i : ℕ) : 0 ≤ primeWeight B i := by
  unfold primeWeight
  split_ifs
  · exact Real.log_natCast_nonneg i
  · exact le_rfl
end GroundTheory.Heights₂.Heights.RestTerms.Elem
