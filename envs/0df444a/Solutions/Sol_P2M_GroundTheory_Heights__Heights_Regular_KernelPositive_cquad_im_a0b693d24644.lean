-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_cquad_im_a0b693d24644
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:32.849449+00:00
-- url     : https://prove2.me/submissions/c78dffd1-8e2f-4c0a-82ab-0220ac7f84e7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PKernelPositive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.KernelPositive
namespace GroundTheory.Heights₂.Heights.Regular.KernelPositive
theorem _root_.solution {g : ℕ} (v : Fin g → ℝ) (M : Matrix (Fin g) (Fin g) ℂ) :
    (cquad v M).im = v ⬝ᵥ (M.map Complex.im *ᵥ v) := by
  simp [cquad, dotProduct, mulVec, Complex.im_sum, Complex.mul_im]
end GroundTheory.Heights₂.Heights.Regular.KernelPositive
