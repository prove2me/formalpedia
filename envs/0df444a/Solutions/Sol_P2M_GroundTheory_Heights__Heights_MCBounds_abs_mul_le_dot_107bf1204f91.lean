-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_abs_mul_le_dot_107bf1204f91
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:41:25.15887+00:00
-- url     : https://prove2.me/submissions/b3bd146b-3974-46b5-93e8-fee7c3e6a1ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_mul_self_le_dot_0fb21db0fb0f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCBounds
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.MCBounds
theorem _root_.solution {ι : Type*} [Fintype ι] (x : ι → ℝ) (j k : ι) :
    |x j| * |x k| ≤ x ⬝ᵥ x := by
  have hj := mul_self_le_dot x j
  have hk := mul_self_le_dot x k
  nlinarith [abs_mul_abs_self (x j), abs_mul_abs_self (x k), sq_nonneg (|x j| - |x k|)]
end GroundTheory.Heights₂.Heights.MCBounds
