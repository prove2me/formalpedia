-- Prove2me | solution 1 for ReciprocityTheory.PTheta.sphereQuadraticPositivity.norm_eC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:48.384538+00:00
-- url     : https://prove2.me/submissions/0ef87958-cc4d-451d-91aa-a676ea67f30f

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta ReciprocityTheory.PTheta.sphereQuadraticPositivity
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.PTheta.sphereQuadraticPositivity
theorem _root_.solution (w : ℂ) : ‖eC w‖ = Real.exp (-2 * Real.pi * w.im) := by
  unfold eC
  rw [Complex.norm_exp]
  congr 1
  simp
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
