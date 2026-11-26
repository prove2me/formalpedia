-- Prove2me | solution 1 for P2M_MeasureTheory_AnalyticSet_union__2545ead870ad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:56.394842+00:00
-- url     : https://prove2.me/submissions/901c9703-c8e4-473c-8659-6b923d7b2a89

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LowerSemianalytic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral

set_option autoImplicit false
open Set Topology MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal
noncomputable section
namespace MeasureTheory.AnalyticSet
theorem _root_.solution
    {W : Type*} [TopologicalSpace W]
    {S T : Set W} (hS : AnalyticSet S) (hT : AnalyticSet T) :
    AnalyticSet (S ∪ T) := by
  have h : S ∪ T = ⋃ b : Bool, (bif b then S else T) := by
    ext w; simp [Bool.exists_bool, or_comm]
  rw [h]
  exact AnalyticSet.iUnion fun b => by cases b <;> simpa
end MeasureTheory.AnalyticSet
