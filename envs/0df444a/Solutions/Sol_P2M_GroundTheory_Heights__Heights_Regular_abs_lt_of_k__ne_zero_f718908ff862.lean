-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_abs_lt_of_k__ne_zero_f718908ff862
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:49:38.764087+00:00
-- url     : https://prove2.me/submissions/1df31cec-68a6-429a-af7e-352c6abed3d3

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_RegMaxReindex

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
open MeasureTheory
open ReciprocityTheory.AnForm.A (regMax tmax kθ)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {x : ℝ} (h : kθ x ≠ 0) : |x| < 1 / 2 := by
  have hs : x ∈ Function.support kθ := h
  unfold kθ at hs
  rw [ContDiffBump.support_normed_eq] at hs
  simpa [Real.dist_eq] using hs
end GroundTheory.Heights₂.Heights.Regular
