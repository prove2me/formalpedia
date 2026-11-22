-- Prove2me | solution 1 for ProbabilityTheory.measurable_sigmaCurry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:43:46.918+00:00
-- url     : https://prove2.me/submissions/1f944053-d7a0-4d81-b940-6a32ed8ad274

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
variable {ι Ω : Type*} {κ : ι → Type*} {α : ∀ i,
  κ i → Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [m : ∀ i j, MeasurableSpace (α i j)] {f : ∀ i j, Ω → α i j}
namespace ProbabilityTheory
theorem _root_.solution :
    Measurable (Sigma.curry : (∀ ij : Σ i, κ i, α ij.1 ij.2) → ∀ i j, α i j) := by
  measurability
end ProbabilityTheory
