-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_hasFDerivAt_partial_f6bd2ae7e203
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:03:44.773257+00:00
-- url     : https://prove2.me/submissions/339fcc57-f29c-4cd9-b07b-09ad501ab375

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFsPotLaplacian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PFsPotLaplacian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open InnerProductSpace Laplacian Real MeasureTheory Filter Topology Set
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution (y e : ℂ) :
    HasFDerivAt (fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹ * (z.re * e.re + z.im * e.im))
      ((1 + ‖y‖ ^ 2)⁻¹ • (e.re • Complex.reCLM + e.im • Complex.imCLM) +
        (y.re * e.re + y.im * e.im) •
          (-(((1 + ‖y‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ y))) y := by
  have h1 : HasFDerivAt (fun z : ℂ => 1 + ‖z‖ ^ 2) (2 • innerSL ℝ y) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_add 1
  have h2 : HasFDerivAt (fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-((1 + ‖y‖ ^ 2) ^ 2)⁻¹)).comp
        (2 • innerSL ℝ y)) y :=
    (hasFDerivAt_inv (by positivity : (1 + ‖y‖ ^ 2) ≠ 0)).comp y h1
  have h3 : HasFDerivAt (fun z : ℂ => z.re * e.re + z.im * e.im)
      (e.re • Complex.reCLM + e.im • Complex.imCLM) y := by
    have hf : (fun z : ℂ => z.re * e.re + z.im * e.im) =
        fun z => (e.re • Complex.reCLM + e.im • Complex.imCLM) z := by
      funext z; simp; ring
    rw [hf]
    exact ContinuousLinearMap.hasFDerivAt _
  refine (h2.mul h3).congr_fderiv ?_
  ext w
  simp <;> ring_nf <;> simp
end GroundTheory.Heights₂.Heights.LowerBoundFree
