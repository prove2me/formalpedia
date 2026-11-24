-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_RestConstants_intersectionNumber_baseChange_3cbe9c9bc2bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:43.605812+00:00
-- url     : https://prove2.me/submissions/9d3869fb-fbe8-431d-b33e-9216f4aa44e8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_two_log_four_le_07c7efd7ce7c

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
namespace RestConstants
theorem _root_.solution : RestConstants.Statement := by
  refine ⟨two_log_four_le, ?_⟩
  intro f N hf hN
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hN' : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have : (1.5 : ℝ) * f * (3 / 2 * (N : ℝ) ^ 2) * (2.78 / (4 * f * (N : ℝ) ^ 2)) =
      1.5 * (3 / 2) * 2.78 / 4 := by
    field_simp
  rw [this]
  norm_num
end RestConstants
end GroundTheory.Heights₂.Heights.RestTerms
