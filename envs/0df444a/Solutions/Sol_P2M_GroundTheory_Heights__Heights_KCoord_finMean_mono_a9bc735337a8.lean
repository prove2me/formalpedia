-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KCoord_finMean_mono_a9bc735337a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:00:52.764337+00:00
-- url     : https://prove2.me/submissions/5cce7549-dad6-4103-baa7-86e7105c125f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CoordWeak
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_card_pos_real_b5d9ffd13cbb

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
open Real
open GroundTheory.Heights₂.Heights.KCoord
variable {S : Type*} [Fintype S]
namespace GroundTheory.Heights₂.Heights.KCoord
theorem _root_.solution [Nonempty S] {f h : S → ℝ} (hfh : ∀ s, f s ≤ h s) : finMean f ≤ finMean h :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun s _ => hfh s) card_pos_real.le
end GroundTheory.Heights₂.Heights.KCoord
