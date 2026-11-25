-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_blockOut_1bbd3daf3e2a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:43:43.397098+00:00
-- url     : https://prove2.me/submissions/90155c5b-9c95-4460-9c60-43895728727f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_antitone_of_mem_partitionsOf_9fba049ce9d8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_pushOut_sum_c0d7e90ce723
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_rectangle_mem_partitionsOf_35563b48a979

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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (r a : ℕ) (c : SmallBlock) (κ : ℚ) (q m : ℕ) :
    constantCoeff (blockOut r a c κ q m) =
      if q + m = r * a then blockCoeff q m (rectangle r a) * κ else 0 := by
  rw [blockOut, constantCoeff_pushOut_sum r a c κ _ (fun lam h => antitone_of_mem_partitionsOf h)]
  by_cases h : q + m = r * a
  · rw [if_pos ((rectangle_mem_partitionsOf r a (q + m)).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((rectangle_mem_partitionsOf r a (q + m)).mp h')), if_neg h]
end GroundTheory.Heights₂.Heights.RestTerms.Top
