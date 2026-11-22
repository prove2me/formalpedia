-- Prove2me | solution 1 for ProbabilityTheory.Kernel.condKernel_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:37:34.069417+00:00
-- url     : https://prove2.me/submissions/82ecf6a5-beb3-48b4-a603-78666bf02192

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration

set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory Measure ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace T] [MeasurableSpace U]
open ProbabilityTheory.Kernel
variable [Countable U] [Nonempty U] [DiscreteMeasurableSpace U]
namespace ProbabilityTheory.Kernel
theorem _root_.solution (κ : Kernel T (S × U)) [IsFiniteKernel κ] (x : T × S)
    (hx : κ x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0) :
    condKernel κ x = (κ x.1).condKernel x.2 := by
  have h := condKernel_apply_eq_condKernel κ x.1
  rw [Filter.EventuallyEq, ae_iff_of_countable] at h
  refine h x.2 ?_
  rwa [fst_apply' _ _ (.singleton _)]
end ProbabilityTheory.Kernel
