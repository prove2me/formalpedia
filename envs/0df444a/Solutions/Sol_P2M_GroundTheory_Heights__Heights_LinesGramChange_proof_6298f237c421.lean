-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesGramChange_proof_6298f237c421
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:36:52.031798+00:00
-- url     : https://prove2.me/submissions/fb0442d8-d5dd-4b86-8df1-5910bce86670

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGramChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGramChange_gramAt_eq_5016030237f4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGramChange_colMatrix_transform_3eb1247b4e10

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
open Matrix
open KLinesGramChange
namespace GroundTheory.Heights₂.Heights
namespace LinesGramChange
theorem _root_.solution : LinesGramChange.Statement := by
  intro K _ n h σ ι _ u P
  rw [gramAt_eq, gramAt_eq, colMatrix_transform, conjTranspose_mul]
  simp only [Matrix.mul_assoc]
end LinesGramChange
end GroundTheory.Heights₂.Heights
