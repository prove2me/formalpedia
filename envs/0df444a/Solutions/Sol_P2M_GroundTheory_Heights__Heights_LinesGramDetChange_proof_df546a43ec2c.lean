-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesGramDetChange_proof_df546a43ec2c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:34.787854+00:00
-- url     : https://prove2.me/submissions/afcc456a-2d7b-4165-a566-60e0cdfba964

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGramDetChange

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
namespace GroundTheory.Heights₂.Heights
namespace LinesGramDetChange
theorem _root_.solution (h1 : LinesGramChange.Statement) :
    LinesGramDetChange.Statement := by
  intro K _ n h σ ι _ _ B u
  have hu : u = fun a => ∑ b, B.toMatrix u b a • B b := by
    funext a
    exact (B.sum_toMatrix_smul_self u a).symm
  have hg := h1 K n h σ ι (⇑B) (B.toMatrix u)
  rw [← hu] at hg
  rw [hg, det_mul, det_mul, det_conjTranspose, RingHom.map_det]
  simp only [RingHom.mapMatrix_apply]
  ring
end LinesGramDetChange
end GroundTheory.Heights₂.Heights
