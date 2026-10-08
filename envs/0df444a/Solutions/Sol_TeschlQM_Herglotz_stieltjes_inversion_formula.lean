-- Prove2me | solution 1 for TeschlQM.Herglotz.stieltjes_inversion_formula
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-05T03:50:23.884888+00:00
-- url     : https://prove2.me/submissions/307e0ac5-3da6-4aa2-8aa2-bae49eb2a1f0

import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Theorems.Thm_RealPoisson_interval_arctan_mass_tendsto
import Theorems.Thm_TeschlQM_Herglotz_borelTransform_im
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum

open MeasureTheory Filter Set
open scoped Topology

namespace HerglotzStieltjes

noncomputable def intervalKernel (a b ε x : ℝ) : ℝ :=
  (Real.arctan ((b - x) / ε) - Real.arctan ((a - x) / ε)) / Real.pi
theorem integral_poisson_interval (a b ε x : ℝ) (hε : 0 < ε) :
    (∫ t in a..b, ε / ((x - t)^2 + ε^2)) =
      Real.arctan ((b - x) / ε) - Real.arctan ((a - x) / ε) := by
  have hi := integral_inv_sq_add_sq (a := a - x) (b := b - x) hε.ne'
  calc
    _ = ε * ∫ t in a..b, (ε^2 + (t - x)^2)⁻¹ := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      ext t
      rw [div_eq_mul_inv]
      congr 2
      ring
    _ = ε * ∫ t in a - x..b - x, (ε^2 + t^2)⁻¹ := by
      rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => (ε^2 + t^2)⁻¹) x]
    _ = _ := by rw [hi]; field_simp

theorem poisson_le_inv (x t ε : ℝ) (hε : 0 < ε) :
    ‖ε / ((x - t)^2 + ε^2)‖ ≤ ε⁻¹ := by
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ (by positivity : 0 < (x-t)^2 + ε^2)).mpr
  calc
    ε = ε⁻¹ * ε^2 := by field_simp
    _ ≤ ε⁻¹ * ((x-t)^2 + ε^2) := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (x-t)]) (by positivity)

theorem normalized_integral_eq (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b ε : ℝ) (hε : 0 < ε) :
    (1 / Real.pi) * (∫ t in a..b,
      (TeschlQM.Herglotz.borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im) =
      ∫ x : ℝ, intervalKernel a b ε x ∂μ := by
  have hc : Continuous (fun p : ℝ × ℝ => ε / ((p.2 - p.1)^2 + ε^2)) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro p
    positivity
  have : IsFiniteMeasure (volume.restrict (uIoc a b)) := by
    rcases le_total a b with h | h
    · rw [uIoc_of_le h]; infer_instance
    · rw [uIoc_of_ge h]; infer_instance
  have hi : Integrable (fun p : ℝ × ℝ => ε / ((p.2 - p.1)^2 + ε^2))
      ((volume.restrict (uIoc a b)).prod μ) :=
    Integrable.of_bound hc.aestronglyMeasurable ε⁻¹
      (Eventually.of_forall fun p => poisson_le_inv p.2 p.1 ε hε)
  simp_rw [TeschlQM.Herglotz.borelTransform_im μ _ ε hε]
  rw [intervalIntegral_integral_swap hi, ← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change (1 / Real.pi) * (∫ t in a..b, ε / ((x-t)^2 + ε^2)) = _
  rw [integral_poisson_interval a b ε x hε]
  simp [intervalKernel, div_eq_mul_inv, mul_comm]

end HerglotzStieltjes

open HerglotzStieltjes

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) (hab : a < b) :
    Tendsto (fun ε : ℝ => (1 / Real.pi) * (∫ t in a..b,
      (TeschlQM.Herglotz.borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im))
      (𝓝[>] 0) (𝓝 (((μ (Ioo a b)).toReal + (μ (Icc a b)).toReal) / 2)) := by
  apply (RealPoisson.interval_arctan_mass_tendsto μ a b hab).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (normalized_integral_eq μ a b ε hε).symm

