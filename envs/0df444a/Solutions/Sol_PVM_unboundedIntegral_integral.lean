-- Prove2me | solution 1 for PVM.unboundedIntegral_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:47.621803+00:00
-- url     : https://prove2.me/submissions/4ae71214-c76a-4956-9aa1-e1e7e0c1bf86

import Definitions.Def_Spectral_PVM_Integral
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_Spectral_PVM_Unbounded
import Theorems.Thm_PVM_ofReal_norm_sq_integral_sub_unboundedIntegral
import Theorems.Thm_PVM_integral_mul
import Theorems.Thm_PVM_integral_sub
import Theorems.Thm_PVM_simpleIntegral_one
import Theorems.Thm_PVM_simpleIntegral_zero
attribute [local simp] PVM.simpleIntegral_one
attribute [local simp] PVM.simpleIntegral_zero


section
open MeasureTheory
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem boundedTruncation_sub_error_measurable
    (g : ℝ → ℂ) (hg : Measurable g) (n : ℕ) :
    Measurable (fun r =>
      (↑(‖boundedTruncation g n r - g r‖₊ ^ 2) : ENNReal)) := by
  have hnorm := ((boundedTruncation_measurable g hg n).sub hg).nnnorm.pow_const 2
  exact hnorm.coe_nnreal_ennreal
private theorem boundedTruncation_sub_error_le
    (g : ℝ → ℂ) (n : ℕ) (r : ℝ) :
    (↑(‖boundedTruncation g n r - g r‖₊ ^ 2) : ENNReal) ≤
      (↑(‖g r‖₊ ^ 2) : ENNReal) := by
  by_cases hr : ‖g r‖ ≤ n
  · rw [boundedTruncation, if_pos hr, sub_self, nnnorm_zero,
      zero_pow (by omega)]
    exact bot_le
  · rw [boundedTruncation, if_neg hr, zero_sub, nnnorm_neg]
private theorem boundedTruncation_sub_error_tendsto_zero
    (g : ℝ → ℂ) (r : ℝ) :
    Filter.Tendsto
      (fun n => (↑(‖boundedTruncation g n r - g r‖₊ ^ 2) : ENNReal))
      Filter.atTop (nhds 0) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖g r‖
  refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
  rw [boundedTruncation, if_pos, sub_self, nnnorm_zero,
    zero_pow (by omega), ENNReal.coe_zero]
  exact hN.trans (Nat.cast_le.2 hn)
private theorem PVM.lintegral_boundedTruncation_sub_error_tendsto_zero
    (E_pvm : PVM E) (g : ℝ → ℂ) (hg : Measurable g)
    (x : (E_pvm.unboundedIntegral g hg).domain) :
    Filter.Tendsto
      (fun n => ∫⁻ r,
        (↑(‖boundedTruncation g n r - g r‖₊ ^ 2) : ENNReal)
          ∂E_pvm.scalarMeasure (x : E))
      Filter.atTop (nhds 0) := by
  have h := tendsto_lintegral_of_dominated_convergence
    (μ := E_pvm.scalarMeasure (x : E))
    (F := fun n r =>
      (↑(‖boundedTruncation g n r - g r‖₊ ^ 2) : ENNReal))
    (f := fun _ => 0)
    (fun r => (↑(‖g r‖₊ ^ 2) : ENNReal))
    (fun n => boundedTruncation_sub_error_measurable g hg n)
    (fun n => ae_of_all _ fun r => boundedTruncation_sub_error_le g n r)
    x.property.ne
    (ae_of_all _ fun r => boundedTruncation_sub_error_tendsto_zero g r)
  simpa only [lintegral_zero] using h
omit [InnerProductSpace ℂ E] [CompleteSpace E] in
private theorem tendsto_of_ofReal_norm_sq_sub_tendsto_zero
    {u : ℕ → E} {y : E}
    (h : Filter.Tendsto
      (fun n => ENNReal.ofReal (‖u n - y‖ ^ 2)) Filter.atTop (nhds 0)) :
    Filter.Tendsto u Filter.atTop (nhds y) := by
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  have hsq : Filter.Tendsto (fun n => ‖u n - y‖ ^ 2)
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.toReal_zero] using hreal
  have hnorm := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_zero] using hnorm
private theorem PVM.tendsto_integral_boundedTruncation
    (E_pvm : PVM E) (g : ℝ → ℂ) (hg : Measurable g)
    (x : (E_pvm.unboundedIntegral g hg).domain) :
    Filter.Tendsto
      (fun n => E_pvm.integral (boundedTruncation g n)
        (boundedTruncation_measurable g hg n)
        ⟨n, norm_boundedTruncation_le g n⟩ (x : E))
      Filter.atTop (nhds (E_pvm.unboundedIntegral g hg x)) := by
  apply tendsto_of_ofReal_norm_sq_sub_tendsto_zero
  have herr := E_pvm.lintegral_boundedTruncation_sub_error_tendsto_zero g hg x
  apply herr.congr'
  apply Filter.Eventually.of_forall
  intro n
  simpa only [ENNReal.coe_pow] using
    (E_pvm.ofReal_norm_sq_integral_sub_unboundedIntegral
      (boundedTruncation g n) (boundedTruncation_measurable g hg n)
      ⟨n, norm_boundedTruncation_le g n⟩ g hg x).symm
private theorem sub_bounded
    (f g : ℝ → ℂ) (hf : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (hg : ∃ C, ∀ r, ‖g r‖ ≤ C) :
    ∃ C, ∀ r, ‖f r - g r‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C + D, fun r => ?_⟩
  exact (norm_sub_le (f r) (g r)).trans (add_le_add (hC r) (hD r))
private theorem boundedTruncation_mul_sub_error_measurable
    (g f : ℝ → ℂ) (hg : Measurable g) (hf : Measurable f) (n : ℕ) :
    Measurable (fun r =>
      (↑(‖boundedTruncation g n r * f r - g r * f r‖₊ ^ 2) : ENNReal)) := by
  have hnorm := ((((boundedTruncation_measurable g hg n).mul hf).sub
    (hg.mul hf)).nnnorm.pow_const 2)
  exact hnorm.coe_nnreal_ennreal
private theorem boundedTruncation_mul_sub_error_le
    (g f : ℝ → ℂ) (n : ℕ) (r : ℝ) :
    (↑(‖boundedTruncation g n r * f r - g r * f r‖₊ ^ 2) : ENNReal) ≤
      (↑(‖g r * f r‖₊ ^ 2) : ENNReal) := by
  by_cases hr : ‖g r‖ ≤ n
  · rw [boundedTruncation, if_pos hr, sub_self, nnnorm_zero,
      zero_pow (by omega)]
    exact bot_le
  · rw [boundedTruncation, if_neg hr, zero_mul, zero_sub, nnnorm_neg]
private theorem boundedTruncation_mul_sub_error_tendsto_zero
    (g f : ℝ → ℂ) (r : ℝ) :
    Filter.Tendsto
      (fun n =>
        (↑(‖boundedTruncation g n r * f r - g r * f r‖₊ ^ 2) : ENNReal))
      Filter.atTop (nhds 0) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖g r‖
  refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
  rw [boundedTruncation, if_pos, sub_self, nnnorm_zero,
    zero_pow (by omega), ENNReal.coe_zero]
  exact hN.trans (Nat.cast_le.2 hn)
private theorem PVM.tendsto_integral_boundedTruncation_mul
    (E_pvm : PVM E) (g f : ℝ → ℂ) (hg : Measurable g) (hf : Measurable f)
    (hfBdd : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (hprodBdd : ∃ C, ∀ r, ‖(g * f) r‖ ≤ C) (x : E) :
    Filter.Tendsto
      (fun n => E_pvm.integral (boundedTruncation g n * f)
        ((boundedTruncation_measurable g hg n).mul hf)
        (boundedTruncation_mul_bounded g f n hfBdd) x)
      Filter.atTop
      (nhds (E_pvm.integral (g * f) (hg.mul hf) hprodBdd x)) := by
  apply tendsto_of_ofReal_norm_sq_sub_tendsto_zero
  have htargetL2 := E_pvm.ofReal_norm_sq_integral
    (g * f) (hg.mul hf) hprodBdd x
  have hdomFinite :
      (∫⁻ r, (↑(‖g r * f r‖₊ ^ 2) : ENNReal)
        ∂E_pvm.scalarMeasure x) ≠ ⊤ := by
    have htargetL2' : ENNReal.ofReal
        (‖E_pvm.integral (g * f) (hg.mul hf) hprodBdd x‖ ^ 2) =
        ∫⁻ r, (↑(‖g r * f r‖₊ ^ 2) : ENNReal)
          ∂E_pvm.scalarMeasure x := by
      simpa only [Pi.mul_apply, ENNReal.coe_pow] using htargetL2
    rw [← htargetL2']
    exact ENNReal.ofReal_ne_top
  have herr : Filter.Tendsto
      (fun n => ∫⁻ r,
        (↑(‖boundedTruncation g n r * f r - g r * f r‖₊ ^ 2) : ENNReal)
          ∂E_pvm.scalarMeasure x)
      Filter.atTop (nhds 0) := by
    have h := tendsto_lintegral_of_dominated_convergence
      (μ := E_pvm.scalarMeasure x)
      (F := fun n r =>
        (↑(‖boundedTruncation g n r * f r - g r * f r‖₊ ^ 2) : ENNReal))
      (f := fun _ => 0)
      (fun r => (↑(‖g r * f r‖₊ ^ 2) : ENNReal))
      (fun n => boundedTruncation_mul_sub_error_measurable g f hg hf n)
      (fun n => ae_of_all _ fun r => boundedTruncation_mul_sub_error_le g f n r)
      hdomFinite
      (ae_of_all _ fun r => boundedTruncation_mul_sub_error_tendsto_zero g f r)
    simpa only [lintegral_zero] using h
  apply herr.congr'
  apply Filter.Eventually.of_forall
  intro n
  let fn : ℝ → ℂ := boundedTruncation g n * f
  let p : ℝ → ℂ := g * f
  have hfn : Measurable fn := (boundedTruncation_measurable g hg n).mul hf
  have hp : Measurable p := hg.mul hf
  have hfnBdd : ∃ C, ∀ r, ‖fn r‖ ≤ C :=
    boundedTruncation_mul_bounded g f n hfBdd
  have hsubBdd : ∃ C, ∀ r, ‖fn r - p r‖ ≤ C :=
    sub_bounded fn p hfnBdd hprodBdd
  have hL2 := E_pvm.ofReal_norm_sq_integral (fn - p)
    (hfn.sub hp) hsubBdd x
  rw [E_pvm.integral_sub fn p hfn hp hfnBdd hprodBdd hsubBdd] at hL2
  simpa only [fn, p, Pi.mul_apply, Pi.sub_apply, sub_apply,
    ENNReal.coe_pow] using hL2.symm
open Filter
end

set_option autoImplicit false
open MeasureTheory
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution
    (E_pvm : PVM E) (f : ℝ → ℂ) (hf : Measurable f)
    (hfBdd : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (g : ℝ → ℂ) (hg : Measurable g)
    (hprodBdd : ∃ C, ∀ r, ‖(g * f) r‖ ≤ C) (x : E) :
    E_pvm.unboundedIntegral g hg
        ⟨E_pvm.integral f hf hfBdd x,
          E_pvm.integral_mem_domain_unboundedIntegral
            f hf hfBdd g hg hprodBdd x⟩ =
      E_pvm.integral (g * f) (hg.mul hf) hprodBdd x := by
  let z : (E_pvm.unboundedIntegral g hg).domain :=
    ⟨E_pvm.integral f hf hfBdd x,
      E_pvm.integral_mem_domain_unboundedIntegral
        f hf hfBdd g hg hprodBdd x⟩
  have hleft := E_pvm.tendsto_integral_boundedTruncation g hg z
  have hright := E_pvm.tendsto_integral_boundedTruncation_mul
    g f hg hf hfBdd hprodBdd x
  have hseq (n : ℕ) :
      E_pvm.integral (boundedTruncation g n)
          (boundedTruncation_measurable g hg n)
          ⟨n, norm_boundedTruncation_le g n⟩ (z : E) =
        E_pvm.integral (boundedTruncation g n * f)
          ((boundedTruncation_measurable g hg n).mul hf)
          (boundedTruncation_mul_bounded g f n hfBdd) x := by
    have hop := E_pvm.integral_mul (boundedTruncation g n) f
      (boundedTruncation_measurable g hg n) hf
      ⟨n, norm_boundedTruncation_le g n⟩ hfBdd
      (boundedTruncation_mul_bounded g f n hfBdd)
    have happ := congrArg (fun T : E →L[ℂ] E => T x) hop
    simpa only [mul_apply_eq_comp, z] using happ.symm
  have hleft' : Filter.Tendsto
      (fun n => E_pvm.integral (boundedTruncation g n * f)
        ((boundedTruncation_measurable g hg n).mul hf)
        (boundedTruncation_mul_bounded g f n hfBdd) x)
      Filter.atTop (nhds (E_pvm.unboundedIntegral g hg z)) := by
    apply hleft.congr'
    exact Filter.Eventually.of_forall hseq
  change E_pvm.unboundedIntegral g hg z = _
  exact tendsto_nhds_unique hleft' hright
end PVM
