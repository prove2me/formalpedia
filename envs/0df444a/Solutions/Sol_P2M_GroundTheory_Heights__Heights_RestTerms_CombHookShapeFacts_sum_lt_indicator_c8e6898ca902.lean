-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombHookShapeFacts_sum_lt_indicator_c8e6898ca902
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:24:10.416288+00:00
-- url     : https://prove2.me/submissions/9bd536dd-b8fc-4f89-84c4-b011d8826c32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombHookShapeFacts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_zero_8589bd36c748


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CombHookShapeFacts
theorem _root_.solution (l : ℕ) :
    ∀ m : ℕ, (∑ i ∈ range m, if i < l then 1 else 0) = min m l := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    split_ifs <;> omega
end CombHookShapeFacts
end GroundTheory.Heights₂.Heights.RestTerms
