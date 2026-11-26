-- Prove2me | solution 1 for PVM.unboundedIntegral_eq_of_proj_eq_on_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:23.047948+00:00
-- url     : https://prove2.me/submissions/aa840221-1020-461f-a3cb-c91a7ac1298e

import Definitions.Def_Spectral_PVM_Integral
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_Spectral_PVM_Unbounded
section
open MeasureTheory
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
open Filter
private theorem PVM.scalarMeasure_eq_of_proj_eq_on_measurable
    (E₁ E₂ : PVM E)
    (hproj : ∀ S : Set ℝ, MeasurableSet S → E₁.proj S = E₂.proj S)
    (x : E) :
    E₁.scalarMeasure x = E₂.scalarMeasure x := by
  apply Measure.ext
  intro S hS
  rw [E₁.scalarMeasure_apply x S hS, E₂.scalarMeasure_apply x S hS]
  unfold PVM.scalarContent
  rw [hproj S hS]
private theorem PVM.simpleIntegral_eq_of_proj_eq_on_measurable
    (E₁ E₂ : PVM E)
    (hproj : ∀ S : Set ℝ, MeasurableSet S → E₁.proj S = E₂.proj S)
    (s : SimpleFunc ℝ ℂ) :
    E₁.simpleIntegral s = E₂.simpleIntegral s := by
  classical
  unfold PVM.simpleIntegral
  apply Finset.sum_congr rfl
  intro z hz
  rw [hproj (s ⁻¹' {z}) (s.measurableSet_fiber z)]
private theorem PVM.integral_eq_of_proj_eq_on_measurable
    (E₁ E₂ : PVM E)
    (hproj : ∀ S : Set ℝ, MeasurableSet S → E₁.proj S = E₂.proj S)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    E₁.integral f hf hbdd = E₂.integral f hf hbdd := by
  unfold PVM.integral
  congr 1
  funext n
  exact PVM.simpleIntegral_eq_of_proj_eq_on_measurable E₁ E₂ hproj _
end

set_option autoImplicit false
open MeasureTheory
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
open Filter
namespace PVM
theorem _root_.solution
    (E₁ E₂ : PVM E)
    (hproj : ∀ S : Set ℝ, MeasurableSet S → E₁.proj S = E₂.proj S)
    (f : ℝ → ℂ) (hf : Measurable f) :
    E₁.unboundedIntegral f hf = E₂.unboundedIntegral f hf := by
  apply LinearPMap.ext
  · ext x
    rw [E₁.mem_domain_unboundedIntegral f hf x,
      E₂.mem_domain_unboundedIntegral f hf x,
      PVM.scalarMeasure_eq_of_proj_eq_on_measurable E₁ E₂ hproj x]
  · intro x hx hy
    unfold PVM.unboundedIntegral
    apply congrArg (fun g : ℕ → E => limUnder atTop g)
    funext n
    exact congrArg (fun T : E →L[ℂ] E => T x)
      (PVM.integral_eq_of_proj_eq_on_measurable E₁ E₂ hproj _ _ _)
end PVM
