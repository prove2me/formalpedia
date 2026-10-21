-- Prove2me | solution 1 for ScarceTesting.PerfectTest.dA_dtH
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:05:55.579681+00:00
-- url     : https://prove2.me/submissions/3a9b1de4-02c9-4ad0-8765-14fc11eaad06

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

set_option autoImplicit false
open MeasureTheory Set Topology ScarceTesting.PerfectTest

theorem solution (f : ℝ → ℝ) (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ < 1) (hf : IsPriorDensity f)
    (hf1 : ContinuousWithinAt f (Set.Icc 0 1) 1) :
    HasDerivWithinAt (fun t => availThr f κ 0 t) (-κ * f 1) (Set.Iic 1) 1 := by
  have hi := hf.integrable
  have hIcc : Icc (0:ℝ) 1 ∈ 𝓝[≤] (1:ℝ) := Icc_mem_nhdsLE zero_lt_one
  have hint : IntegrableOn f (Icc 0 1) volume := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one] at hi
    exact hi
  have hmeas : StronglyMeasurableAtFilter f (𝓝[≤] (1:ℝ)) volume :=
    ⟨Icc 0 1, hIcc, hint.aestronglyMeasurable⟩
  have hcont : ContinuousWithinAt f (Iic 1) 1 := hf1.mono_of_mem_nhdsWithin hIcc
  have hF : HasDerivWithinAt (fun u => ∫ x in (0:ℝ)..u, f x) (f 1) (Iic 1) 1 :=
    intervalIntegral.integral_hasDerivWithinAt_right (s := Iic 1) (t := Iic 1) hi hmeas hcont
  have hF1 : (∫ x in (0:ℝ)..1, f x) = 1 := hf.total
  have hdiv : HasDerivWithinAt (fun t => κ / ∫ x in (0:ℝ)..t, f x)
      ((0 * (∫ x in (0:ℝ)..1, f x) - κ * f 1) / (∫ x in (0:ℝ)..1, f x) ^ 2) (Iic 1) 1 :=
    (hasDerivWithinAt_const (1:ℝ) (Iic 1) κ).div hF (by rw [hF1]; exact one_ne_zero)
  have hev : ∀ᶠ t in 𝓝[Iic 1] (1:ℝ), κ < ∫ x in (0:ℝ)..t, f x :=
    hF.continuousWithinAt.eventually (lt_mem_nhds (by dsimp only; rw [hF1]; exact hκ1))
  have hA : ∀ t : ℝ, κ < ∫ x in (0:ℝ)..t, f x →
      availThr f κ 0 t = κ / ∫ x in (0:ℝ)..t, f x := by
    intro t ht
    have h0 : cdf f 0 = 0 := by simp [cdf]
    have ht' : κ < cdf f t := ht
    unfold availThr availability
    rw [h0, sub_zero, if_neg (not_le.2 ht')]
    rfl
  refine (hdiv.congr_of_eventuallyEq ?_ ?_).congr_deriv ?_
  · filter_upwards [hev] with t ht using hA t ht
  · exact hA 1 (by rw [hF1]; exact hκ1)
  · rw [hF1]; ring
