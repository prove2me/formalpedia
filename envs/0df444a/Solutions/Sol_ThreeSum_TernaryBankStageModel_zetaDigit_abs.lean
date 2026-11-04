-- Prove2me | solution 1 for ThreeSum.TernaryBankStageModel.zetaDigit_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:36:00.089109+00:00
-- url     : https://prove2.me/submissions/248eeb13-3307-4720-91e7-3ff10cfc61ce

import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_Submission_ThreeSum_TernaryBankStageModel

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryBankStageModel
theorem _root_.solution (f : Fin 3→ℤ) (B : ℤ) (hf : ∀ d, |f d|≤B) (q : Fin 3) :
    |zetaDigit f q|≤4*B := by
  have hB : 0≤B := (abs_nonneg (f 0)).trans (hf 0)
  unfold zetaDigit
  split_ifs
  · exact (hf 0).trans (by omega)
  · exact (abs_add_le _ _).trans (by linarith [hf 0,hf 1])
  · have hm : |2*f 1|≤2*B := by rw [abs_mul]; norm_num; linarith [hf 1]
    calc
      |f 0+2*f 1+f 2|≤|f 0+2*f 1|+|f 2| := abs_add_le _ _
      _≤(|f 0|+|2*f 1|)+|f 2| := add_le_add (abs_add_le _ _) le_rfl
      _≤4*B := by linarith [hf 0,hf 2]
end ThreeSum.TernaryBankStageModel
