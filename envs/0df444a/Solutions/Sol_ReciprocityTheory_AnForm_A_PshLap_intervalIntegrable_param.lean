-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.intervalIntegrable_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:36.996865+00:00
-- url     : https://prove2.me/submissions/8f0909b9-48e5-4cd7-bf50-adaac031b909

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution {F : ℝ → ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Icc c d)) :
    IntervalIntegrable (fun x => ∫ y in c..d, F x y) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hI : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have h := hI.integral_prod_left
  simp only [Function.uncurry_apply_pair] at h
  simp only [intervalIntegral.integral_of_le hcd]
  exact h
end ReciprocityTheory.AnForm.A.PshLap
