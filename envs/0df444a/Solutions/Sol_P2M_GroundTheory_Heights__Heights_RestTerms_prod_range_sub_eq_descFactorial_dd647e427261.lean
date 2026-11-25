-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_prod_range_sub_eq_descFactorial_dd647e427261
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:13:33.231819+00:00
-- url     : https://prove2.me/submissions/b09e8f36-94b4-4c6a-9991-11d8ae03c0a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableEqCardMonotone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookTableauCount
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
theorem _root_.solution (n l : ℕ) :
    ∏ j ∈ Finset.range l, (n - j) = n.descFactorial l := by
  induction l with
  | zero => simp
  | succ l ih => rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ, mul_comm]
end GroundTheory.Heights₂.Heights.RestTerms
