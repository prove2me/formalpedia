-- Prove2me | solution 1 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.enorm_sub_le_enorm_mul_lintegral_grad
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:04:03.161587+00:00
-- url     : https://prove2.me/submissions/6f74800a-6cc2-4430-88af-4417367eccc8

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_H1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimate
set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceTranslationEstimate
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpaceTranslationEstimate
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instOpensMeasurableSpaceTranslationEstimate
variable [CompleteSpace E]

private lemma deriv_comp_line (x a : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) (t : ℝ) :
    deriv (fun t : ℝ => f (x + t • a)) t = fderiv ℝ f (x + t • a) a := by
  have hline : HasDerivAt (fun t : ℝ => x + t • a) a t := by
    convert (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const a) using 1 <;>
      simp [funext_iff]
  have hcomp := (hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp_hasDerivAt
    t hline
  change deriv (f ∘ fun t : ℝ => x + t • a) t = fderiv ℝ f (x + t • a) a
  exact hcomp.deriv

private lemma enorm_deriv_comp_line_le_aux (x a : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (t : ℝ) : ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ ≤
      ‖a‖ₑ * ‖grad (E := E) f (x + t • a)‖ₑ := by
  rw [deriv_comp_line x a hf t]
  calc
    ‖fderiv ℝ f (x + t • a) a‖ₑ ≤ ‖fderiv ℝ f (x + t • a)‖ₑ * ‖a‖ₑ :=
      ContinuousLinearMap.le_opENorm (f := fderiv ℝ f (x + t • a)) a
    _ = ‖grad (E := E) f (x + t • a)‖ₑ * ‖a‖ₑ := by
      have hnorm : ‖grad (E := E) f (x + t • a)‖ₑ = ‖fderiv ℝ f (x + t • a)‖ₑ := by
        simp only [grad]
        exact LinearIsometry.enorm_map
          (f := (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry)
          (fderiv ℝ f (x + t • a))
      rw [hnorm]
    _ = ‖a‖ₑ * ‖grad (E := E) f (x + t • a)‖ₑ := mul_comm _ _

theorem solution (x a : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    ‖f (x + a) - f x‖ₑ ≤
      ‖a‖ₑ * ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖grad (E := E) f (x + t • a)‖ₑ := by
  have hCont :
      ContDiffOn ℝ 1 (fun t : ℝ => f (x + t • a)) (Set.Icc (0 : ℝ) 1) := by
    have hInner : ContDiff ℝ ⊤ (fun t : ℝ => x + t • a) := by
      simpa [line] using
        (contDiff_const.add (contDiff_id.smul (contDiff_const :
          ContDiff ℝ ⊤ (fun _ : ℝ => a))))
    have hInner' : ContDiff ℝ 1 (fun t : ℝ => x + t • a) := hInner.of_le (by simp)
    exact (hf.comp hInner').contDiffOn
  have hFTC :
      ‖f (x + a) - f x‖ₑ ≤
        ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ := by
    simpa using
      (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc
        (f := fun t : ℝ => f (x + t • a)) (a := (0 : ℝ)) (b := 1) hCont
        (by exact zero_le_one))
  refine hFTC.trans ?_
  have hDerivBound :
      (fun t : ℝ => ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ)
        ≤ᵐ[Measure.restrict volume (Set.Icc (0 : ℝ) 1)]
          fun t : ℝ => ‖a‖ₑ * ‖grad (E := E) f (x + t • a)‖ₑ := by
    refine ae_of_all _ fun t => ?_
    exact enorm_deriv_comp_line_le_aux x a hf t
  have hIntegral :
      (∫⁻ t in Set.Icc (0 : ℝ) 1, ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ) ≤
        ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖a‖ₑ * ‖grad (E := E) f (x + t • a)‖ₑ := by
    exact lintegral_mono_ae hDerivBound
  refine hIntegral.trans ?_
  have hMeas : Measurable (fun t : ℝ => ‖grad (E := E) f (x + t • a)‖ₑ) := by
    exact ((continuous_grad (E := E) hf).comp (by
      have hline : Continuous (fun t : ℝ => x + t • a) := by fun_prop
      exact hline)).measurable.enorm
  exact le_of_eq <| by
    simpa [mul_assoc] using
      (MeasureTheory.lintegral_const_mul (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
        (r := ‖a‖ₑ) (f := fun t : ℝ => ‖grad (E := E) f (x + t • a)‖ₑ) hMeas)
