-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisS_spec_d0b72175b660
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:54:42.568115+00:00
-- url     : https://prove2.me/submissions/0f157851-eacd-473d-b219-49b576e40eed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_self_im_82678c31a9eb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι]
variable {H : Matrix ι ι ℂ}
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (hH : H.IsHermitian) (y : ι → ℂ) (t : ℝ) :
    heisS H y t + starRingEnd ℂ (heisS H y t) + hForm H y y = 0 := by
  apply Complex.ext
  · simp only [heisS, Complex.add_re, Complex.conj_re, Complex.zero_re]
    ring
  · simp only [heisS, Complex.add_im, Complex.conj_im, Complex.zero_im, hForm_self_im hH]
    ring
end GroundTheory.Heights₂.Heights.FiniteCovolume
