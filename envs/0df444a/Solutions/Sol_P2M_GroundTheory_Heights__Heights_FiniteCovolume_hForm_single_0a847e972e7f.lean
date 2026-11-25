-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_single_0a847e972e7f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:54:11.089932+00:00
-- url     : https://prove2.me/submissions/9eab36e9-b2ca-48c3-ba1c-de33874d7a64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix

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
variable (H : Matrix ι ι ℂ)
variable [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (X : Matrix ι ι ℂ) (i j : ι) :
    hForm X (Pi.single i 1) (Pi.single j 1) = X i j := by
  simp [hForm]
end GroundTheory.Heights₂.Heights.FiniteCovolume
