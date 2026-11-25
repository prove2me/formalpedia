-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_mul_self_le_dot_0fb21db0fb0f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:07.310287+00:00
-- url     : https://prove2.me/submissions/2edb8e57-0f7e-466d-9ee5-71c07e2da7dd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY

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
theorem _root_.solution {ι : Type*} [Fintype ι] (x : ι → ℝ) (j : ι) : x j * x j ≤ x ⬝ᵥ x :=
  Finset.single_le_sum (f := fun i => x i * x i) (fun i _ => mul_self_nonneg (x i))
    (Finset.mem_univ j)
end GroundTheory.Heights₂.Heights.MCBounds
