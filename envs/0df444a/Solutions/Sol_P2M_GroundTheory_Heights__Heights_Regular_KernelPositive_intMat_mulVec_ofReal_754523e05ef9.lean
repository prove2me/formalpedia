-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_intMat_mulVec_ofReal_754523e05ef9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:49:25.881019+00:00
-- url     : https://prove2.me/submissions/8b98f228-9213-4045-87d0-6ba74db4ceca

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
theorem _root_.solution {g : ℕ} (B : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℝ)
    (h : B.map (Int.cast : ℤ → ℝ) *ᵥ v = 0) :
    B.map (Int.cast : ℤ → ℂ) *ᵥ (fun k => (v k : ℂ)) = 0 := by
  funext k
  have hk := congrFun h k
  simp only [mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at hk ⊢
  exact_mod_cast hk
end GroundTheory.Heights₂.Heights.Regular.KernelPositive
