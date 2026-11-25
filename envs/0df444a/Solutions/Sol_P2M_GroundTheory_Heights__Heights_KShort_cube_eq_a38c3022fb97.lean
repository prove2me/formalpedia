-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KShort_cube_eq_a38c3022fb97
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:01:21.322057+00:00
-- url     : https://prove2.me/submissions/cd78c5ef-3817-4a91-8f3b-b547e69ce4da

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ShortVectors

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
open MeasureTheory Module Metric
noncomputable section
open GroundTheory.Heights₂.Heights.KShort
namespace GroundTheory.Heights₂.Heights.KShort
theorem _root_.solution (n : ℕ) (c : ℝ) :
    cube n c = (WithLp.ofLp) ⁻¹' (Set.pi Set.univ fun _ : Fin n => Set.Ioo (-c) c) := by
  ext x; simp [cube, abs_lt]
end GroundTheory.Heights₂.Heights.KShort
