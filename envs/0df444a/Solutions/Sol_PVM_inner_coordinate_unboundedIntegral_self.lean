-- Prove2me | solution 1 for PVM.inner_coordinate_unboundedIntegral_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:03:10.262304+00:00
-- url     : https://prove2.me/submissions/fdf8c9cc-2120-4a9a-86fc-153b407a9de4

import Definitions.Def_Spectral_PVM_Integral
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_Spectral_PVM_Unbounded
import Theorems.Thm_PVM_inner_integral_self
import Theorems.Thm_PVM_simpleIntegral_one
import Theorems.Thm_PVM_simpleIntegral_zero
attribute [local simp] PVM.simpleIntegral_one
attribute [local simp] PVM.simpleIntegral_zero


section
open MeasureTheory
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem PVM.spectralTruncation_tendsto (f : ℝ → ℂ) (t : ℝ) :
    Filter.Tendsto (fun n => PVM.spectralTruncation f n t)
      Filter.atTop (nhds (f t)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖f t‖
  refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
  rw [PVM.spectralTruncation, if_pos]
  exact hN.trans (Nat.cast_le.2 hn)
open Filter
end

set_option autoImplicit false
open MeasureTheory
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E)
    (x : (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable).domain) :
    @inner ℂ E _ (x : E)
        (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
          Complex.continuous_ofReal.measurable x) =
      ∫ t, (t : ℂ) ∂(E_pvm.scalarMeasure (x : E)) := by
  let coord : ℝ → ℂ := (↑)
  let hcoord : Measurable coord := Complex.continuous_ofReal.measurable
  have hxL2 : ∫⁻ t, ‖coord t‖₊ ^ 2
      ∂(E_pvm.scalarMeasure (x : E)) < ⊤ := by
    have hx := x.property
    change (∫⁻ t, ‖((t : ℂ))‖₊ ^ 2
      ∂(E_pvm.scalarMeasure (x : E))) < ⊤ at hx
    simpa only [coord] using hx
  have hsq : Integrable (fun t : ℝ ↦ ‖coord t‖ ^ 2)
      (E_pvm.scalarMeasure (x : E)) := by
    constructor
    · fun_prop
    · rw [hasFiniteIntegral_iff_enorm]
      simpa only [Real.enorm_of_nonneg (sq_nonneg _),
        ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
        using hxL2
  have hmemLp : MemLp coord 2 (E_pvm.scalarMeasure (x : E)) :=
    (memLp_two_iff_integrable_sq_norm hcoord.aestronglyMeasurable).2 hsq
  have hcoordInt : Integrable coord (E_pvm.scalarMeasure (x : E)) :=
    hmemLp.integrable (by norm_num)
  have htrunc :=
    (E_pvm.cauchySeq_truncatedIntegral coord hcoord x).tendsto_limUnder
  change Filter.Tendsto
    (fun n ↦ E_pvm.truncatedIntegral coord hcoord n (x : E))
    Filter.atTop
    (nhds (E_pvm.unboundedIntegral coord hcoord x)) at htrunc
  have hinner : Filter.Tendsto
      (fun n ↦ @inner ℂ E _ (x : E)
        (E_pvm.truncatedIntegral coord hcoord n (x : E)))
      Filter.atTop
      (nhds (@inner ℂ E _ (x : E)
        (E_pvm.unboundedIntegral coord hcoord x))) :=
    Filter.Tendsto.inner tendsto_const_nhds htrunc
  have hintegral : Filter.Tendsto
      (fun n ↦ ∫ t, PVM.spectralTruncation coord n t
        ∂(E_pvm.scalarMeasure (x : E)))
      Filter.atTop
      (nhds (∫ t, coord t ∂(E_pvm.scalarMeasure (x : E)))) := by
    apply tendsto_integral_of_dominated_convergence (fun t ↦ ‖coord t‖)
    · intro n
      exact (PVM.spectralTruncation_measurable coord hcoord n).aestronglyMeasurable
    · exact hcoordInt.norm
    · intro n
      apply ae_of_all
      intro t
      unfold PVM.spectralTruncation
      split_ifs
      · exact le_rfl
      · simp
    · exact ae_of_all _ fun t ↦ PVM.spectralTruncation_tendsto coord t
  apply tendsto_nhds_unique hinner
  simpa only [PVM.truncatedIntegral, E_pvm.inner_integral_self, coord, hcoord]
    using hintegral
end PVM
