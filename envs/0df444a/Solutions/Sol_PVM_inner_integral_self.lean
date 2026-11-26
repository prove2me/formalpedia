-- Prove2me | solution 1 for PVM.inner_integral_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:02:21.874592+00:00
-- url     : https://prove2.me/submissions/edfd40dd-b321-42e2-869b-86dcec83eea7

import Definitions.Def_Spectral_PVM_Integral
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_Spectral_PVM_Unbounded
import Theorems.Thm_PVM_inner_simpleIntegral_self
import Theorems.Thm_PVM_simpleIntegral_one
import Theorems.Thm_PVM_simpleIntegral_zero
import Theorems.Thm_PVM_tendsto_simpleIntegral_of_tendstoUniformly
import Theorems.Thm_exists_bounded_simpleFunc_tendstoUniformly
attribute [local simp] PVM.simpleIntegral_one
attribute [local simp] PVM.simpleIntegral_zero



set_option autoImplicit false
open MeasureTheory
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (x : E) :
    @inner ℂ E _ x (E_pvm.integral f hf hbdd x) =
      ∫ t, f t ∂(E_pvm.scalarMeasure x) := by
  let C : ℝ := Classical.choose hbdd
  have hC : ∀ t, ‖f t‖ ≤ C := Classical.choose_spec hbdd
  obtain ⟨s, hs, hsC⟩ := exists_bounded_simpleFunc_tendstoUniformly f hf C hC
  have hop := E_pvm.tendsto_simpleIntegral_of_tendstoUniformly f hf hbdd s hs
  have happly : Filter.Tendsto
      (fun n => E_pvm.simpleIntegral (s n) x) Filter.atTop
      (nhds (E_pvm.integral f hf hbdd x)) := by
    exact (Continuous.continuousAt
      (Continuous.clm_apply continuous_id continuous_const)).tendsto.comp hop
  have hinner : Filter.Tendsto
      (fun n => @inner ℂ E _ x (E_pvm.simpleIntegral (s n) x))
      Filter.atTop (nhds (@inner ℂ E _ x (E_pvm.integral f hf hbdd x))) := by
    exact Filter.Tendsto.inner (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ => x) Filter.atTop (nhds x)) happly
  have hintegral : Filter.Tendsto
      (fun n => ∫ t, s n t ∂(E_pvm.scalarMeasure x)) Filter.atTop
      (nhds (∫ t, f t ∂(E_pvm.scalarMeasure x))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C)
    · intro n
      exact (s n).measurable.aestronglyMeasurable
    · exact integrable_const C
    · intro n
      exact ae_of_all _ (hsC n)
    · exact ae_of_all _ fun t => hs.tendsto_at t
  apply tendsto_nhds_unique hinner
  simpa only [E_pvm.inner_simpleIntegral_self] using hintegral
end PVM
