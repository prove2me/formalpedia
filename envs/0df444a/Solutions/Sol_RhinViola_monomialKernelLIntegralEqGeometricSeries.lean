-- Prove2me | solution 1 for RhinViola.monomialKernelLIntegralEqGeometricSeries
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:43:42.187437+00:00
-- url     : https://prove2.me/submissions/943aa348-c53b-4c72-8432-7d4c0e70d36f

import Theorems.Thm_RhinViola_weightedGeometricKernelENNRealTsumIoc
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

set_option autoImplicit false

open MeasureTheory

theorem solution
    (h m : ℕ) :
    (∫⁻ x : ℝ in Set.Ioc (0 : ℝ) 1,
      ∫⁻ y : ℝ in Set.Ioc (0 : ℝ) 1,
        ∑' k : ℕ,
          ENNReal.ofReal (x ^ (h + k)) *
            ENNReal.ofReal (y ^ (m + k))) =
      (∫⁻ x : ℝ in Set.Ioc (0 : ℝ) 1,
        ∫⁻ y : ℝ in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal
            (x ^ h * y ^ m / (1 - x * y))) := by
  apply lintegral_congr_ae
  have h1 : ∀ᵐ x : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), x ≠ 1 := by
    apply ae_restrict_of_ae
    have : volume ({1} : Set ℝ) = 0 := measure_singleton 1
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp this] with x hx
    simpa using hx
  have h2 : ∀ᵐ x : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), x ∈ Set.Ioc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioc
  filter_upwards [h1, h2] with x hx1 hx
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro y hy
  exact RhinViola.weightedGeometricKernelENNRealTsumIoc h m x y hx hy hx1
