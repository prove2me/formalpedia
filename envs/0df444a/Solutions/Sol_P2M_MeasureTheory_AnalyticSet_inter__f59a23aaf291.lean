-- Prove2me | solution 1 for P2M_MeasureTheory_AnalyticSet_inter__f59a23aaf291
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:23.542805+00:00
-- url     : https://prove2.me/submissions/9516d19d-1a75-4fdf-a4cb-442822746d4b

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
    {W : Type*} [TopologicalSpace W] [T2Space W]
    {S T : Set W} (hS : AnalyticSet S) (hT : AnalyticSet T) :
    AnalyticSet (S ∩ T) := by
  have h : S ∩ T = ⋂ b : Bool, (bif b then S else T) := by
    ext w; simp [Bool.forall_bool, and_comm]
  rw [h]
  exact AnalyticSet.iInter fun b => by cases b <;> simpa
end MeasureTheory.AnalyticSet
