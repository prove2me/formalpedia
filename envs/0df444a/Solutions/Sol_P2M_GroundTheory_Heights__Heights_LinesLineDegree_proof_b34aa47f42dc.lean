-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesLineDegree_proof_b34aa47f42dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:36.629087+00:00
-- url     : https://prove2.me/submissions/5ce296ac-8061-4b1c-a651-403468f87bf5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLineDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesLineDegree_genIndex_map_of_injective_818d1ee55c6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesLineDegree_single_injective_ea33b9403e45
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesLineDegree_inter_line_12696afb69e9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesLineDegree_span_line_c2140cf00a12
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesLineDegree_gram_line_0ccc6c520227

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
open NumberField Matrix
open scoped nonZeroDivisors
noncomputable section
open KLinesLineDegree
namespace GroundTheory.Heights₂.Heights
namespace LinesLineDegree
theorem _root_.solution : LinesLineDegree.Statement := by
  intro K _ _ n a d x
  unfold subDegree idealIndex
  rw [inter_line, span_line, genIndex_map_of_injective _ (single_injective x)]
  simp only [gram_line]
end LinesLineDegree
end GroundTheory.Heights₂.Heights
