-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshInh.avg_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:29.503357+00:00
-- url     : https://prove2.me/submissions/6260902e-781c-410c-9785-a8947c35df94

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshInh
open MeasureTheory Metric Set Filter Topology Real
noncomputable section
namespace ReciprocityTheory.AnForm.A.PshInh
theorem _root_.solution (a b : ℂ) : Real.circleAverage (fun ζ : ℂ => a + ζ * b) 0 1 = a := by
  have h : DiffContOnCl ℂ (fun ζ : ℂ => a + ζ * b) (ball (0:ℂ) |(1:ℝ)|) :=
    (by fun_prop : Differentiable ℂ (fun ζ : ℂ => a + ζ * b)).diffContOnCl
  simpa using h.circleAverage
end ReciprocityTheory.AnForm.A.PshInh
