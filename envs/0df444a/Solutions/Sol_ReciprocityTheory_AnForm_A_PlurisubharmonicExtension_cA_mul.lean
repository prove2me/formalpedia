-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.cA_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:50.677085+00:00
-- url     : https://prove2.me/submissions/93550324-0c1d-4da6-9ad3-2308f40bd09e

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Real Filter Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
theorem _root_.solution (b : ℝ) (f : ℂ → ℝ) (c : ℂ) (R : ℝ) :
    circleAverage (fun z => b * f z) c R = b * circleAverage f c R := by
  simp only [circleAverage, smul_eq_mul, intervalIntegral.integral_const_mul]; ring
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
