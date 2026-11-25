-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.pgds_cont_polar_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:02:12.565581+00:00
-- url     : https://prove2.me/submissions/d6ccb5e0-a4fa-4d8a-8f09-5ca48db7ef46

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_DiscSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Filter Topology
open Set
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
  have : (fun p : ℝ × ℝ => Complex.polarCoord.symm p) =
      fun p => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I) := by
    funext p; simp [Complex.polarCoord_symm_apply]
  rw [this]; fun_prop
end ReciprocityTheory.GeometryOfNumbersTheory
