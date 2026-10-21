-- Prove2me | solution 1 for ScarceTesting.PerfectTest.dA_dtL
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:05:56.838069+00:00
-- url     : https://prove2.me/submissions/b250c5ab-dda4-408c-b68b-71f1343bd0e7

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

set_option autoImplicit false
open MeasureTheory Set Topology ScarceTesting.PerfectTest

theorem solution (f : ℝ → ℝ) (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ < 1) (hf : IsPriorDensity f)
    (hf0 : ContinuousWithinAt f (Set.Icc 0 1) 0) :
    HasDerivWithinAt (fun t => availThr f κ t 1) (κ * f 0) (Set.Ici 0) 0 := by
  have hi := hf.integrable
  have hIoo : Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT zero_lt_one
  have hIcc : Icc (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Filter.mem_of_superset hIoo Ioo_subset_Icc_self
  have hint : IntegrableOn f (Icc 0 1) volume := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one] at hi
    exact hi
  have hmeas : StronglyMeasurableAtFilter f (𝓝[>] (0:ℝ)) volume :=
    ⟨Icc 0 1, hIcc, hint.aestronglyMeasurable⟩
  have hcont : ContinuousWithinAt f (Ioi 0) 0 := hf0.mono_of_mem_nhdsWithin hIcc
  have hF : HasDerivWithinAt (fun u => ∫ x in (0:ℝ)..u, f x) (f 0) (Ici 0) 0 :=
    intervalIntegral.integral_hasDerivWithinAt_right (s := Ici 0) (t := Ioi 0)
      (IntervalIntegrable.refl) hmeas hcont
  have hF1 : (∫ x in (0:ℝ)..1, f x) = 1 := hf.total
  have hG : HasDerivWithinAt (fun t => (∫ x in (0:ℝ)..1, f x) - ∫ x in (0:ℝ)..t, f x)
      (-f 0) (Ici 0) 0 := hF.const_sub _
  have hG0 : (∫ x in (0:ℝ)..1, f x) - ∫ x in (0:ℝ)..0, f x = 1 := by
    simp [hF1]
  have hdiv : HasDerivWithinAt
      (fun t => κ / ((∫ x in (0:ℝ)..1, f x) - ∫ x in (0:ℝ)..t, f x))
      ((0 * ((∫ x in (0:ℝ)..1, f x) - ∫ x in (0:ℝ)..0, f x) - κ * (-f 0)) /
        ((∫ x in (0:ℝ)..1, f x) - ∫ x in (0:ℝ)..0, f x) ^ 2) (Ici 0) 0 :=
    (hasDerivWithinAt_const (0:ℝ) (Ici 0) κ).div hG (by rw [hG0]; exact one_ne_zero)
  have hev : ∀ᶠ t in 𝓝[Ici 0] (0:ℝ),
      κ < (∫ x in (0:ℝ)..1, f x) - ∫ x in (0:ℝ)..t, f x :=
    hG.continuousWithinAt.eventually (lt_mem_nhds (by dsimp only; rw [hG0]; exact hκ1))
  have hA : ∀ t : ℝ, κ < (∫ x in (0:ℝ)..1, f x) - ∫ x in (0:ℝ)..t, f x →
      availThr f κ t 1 = κ / ((∫ x in (0:ℝ)..1, f x) - ∫ x in (0:ℝ)..t, f x) := by
    intro t ht
    have ht' : κ < cdf f 1 - cdf f t := ht
    unfold availThr availability
    rw [if_neg (not_le.2 ht')]
    rfl
  refine (hdiv.congr_of_eventuallyEq ?_ ?_).congr_deriv ?_
  · filter_upwards [hev] with t ht using hA t ht
  · exact hA 0 (by rw [hG0]; exact hκ1)
  · rw [hG0]; ring
