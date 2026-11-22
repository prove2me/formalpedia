-- Prove2me | solution 1 for ProbabilityTheory.IndepFun.measureReal_inter_preimage_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:43:32.935161+00:00
-- url     : https://prove2.me/submissions/f15b4311-f0da-4d4c-94c5-c1bae5d71d2f

module
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory MeasurableSpace Measure Set
open scoped MeasureTheory ENNReal
open ProbabilityTheory
variable {Ω ι β β' γ : Type*} {κ : ι
  → Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β}
  {g : Ω → β'}
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory.IndepFun
theorem _root_.solution
    {_mβ : MeasurableSpace β}
    {_mβ' : MeasurableSpace β'} (h : IndepFun f g μ) {s : Set β} {t : Set β'}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ.real (f ⁻¹' s ∩ g ⁻¹' t) = μ.real (f ⁻¹' s) * μ.real (g ⁻¹' t) := by
  rw [measureReal_def, h.measure_inter_preimage_eq_mul _ _ hs ht, ENNReal.toReal_mul]; rfl
end _root_.ProbabilityTheory.IndepFun
end ProbabilityTheory
