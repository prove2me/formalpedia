-- Prove2me | solution 1 for ProbabilityTheory.indepFun_zero_measure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:23:43.938683+00:00
-- url     : https://prove2.me/submissions/c6712b39-a0cc-4e7e-8d55-afcee974b2d1

module
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Theorems.Thm_ProbabilityTheory_iIndepFun_inv

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory MeasurableSpace Measure Set
open scoped MeasureTheory ENNReal
open ProbabilityTheory
variable {Ω ι β γ : Type*} {κ : ι → Type*}
variable {β β' γ γ' : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω
  → β} {g : Ω → β'}
variable {Ω' α : Type*} [MeasurableSpace Ω'] [MeasurableSpace α] [MeasurableSpace β]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution {f : Ω → α} {g : Ω
  → β} : IndepFun f g (0 : Measure Ω) := by
  simp [IndepFun]
end _root_.ProbabilityTheory
end ProbabilityTheory
