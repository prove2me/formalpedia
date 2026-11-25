-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussPoissonBound_norm_toLp_sq_fc603c567337
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:45:52.466702+00:00
-- url     : https://prove2.me/submissions/5a63bece-4b02-4e65-8be9-0b68a648e1c5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussPoissonBound
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix Real MeasureTheory
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GroundTheory.Heights₂.Heights.PGaussPoissonBound
namespace GroundTheory.Heights₂.Heights.PGaussPoissonBound
theorem _root_.solution {g : ℕ} (v : Fin g → ℝ) : ‖WithLp.toLp 2 v‖ ^ 2 = v ⬝ᵥ v := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [dotProduct, sq]
end GroundTheory.Heights₂.Heights.PGaussPoissonBound
