-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KThetaSummandNorm_im_dot_real_fce10366cc3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:01:31.743076+00:00
-- url     : https://prove2.me/submissions/1344cccd-22d7-4b66-aa0d-6cfb54bdb8dc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaSummandNorm

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
open Matrix Real
noncomputable section
open GroundTheory.Heights₂.Heights.KThetaSummandNorm
namespace GroundTheory.Heights₂.Heights.KThetaSummandNorm
theorem _root_.solution {g : ℕ} (w c : Fin g → ℝ) :
    ((fun i => (w i : ℂ)) ⬝ᵥ fun i => (c i : ℂ)).im = 0 := by
  simp [dotProduct, Complex.im_sum]
end GroundTheory.Heights₂.Heights.KThetaSummandNorm
