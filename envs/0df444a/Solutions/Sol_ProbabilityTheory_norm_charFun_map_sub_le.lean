-- Prove2me | solution 1 for ProbabilityTheory.norm_charFun_map_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:41:44.188302+00:00
-- url     : https://prove2.me/submissions/d97bec59-50f8-423c-9d4b-3048047c3d28

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal
variable {Ω : Type} [MeasurableSpace Ω]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}
theorem solution [IsProbabilityMeasure μ] {V W : Ω → ℝ}
    (hV : AEMeasurable V μ) (hW : AEMeasurable W μ)
    (hVW : Integrable (fun ω => V ω - W ω) μ) (ξ : ℝ) :
    ‖charFun (μ.map V) ξ - charFun (μ.map W) ξ‖ ≤ |ξ| * ∫ ω, |V ω - W ω| ∂μ := by
  have hgV : AEMeasurable (fun ω => Complex.exp (↑ξ * ↑(V ω) * Complex.I)) μ :=
    Complex.measurable_exp.comp_aemeasurable
      (((Complex.measurable_ofReal.comp_aemeasurable hV).const_mul (↑ξ)).mul_const Complex.I)
  have hgW : AEMeasurable (fun ω => Complex.exp (↑ξ * ↑(W ω) * Complex.I)) μ :=
    Complex.measurable_exp.comp_aemeasurable
      (((Complex.measurable_ofReal.comp_aemeasurable hW).const_mul (↑ξ)).mul_const Complex.I)
  have hbV : ∀ ω, ‖Complex.exp (↑ξ * ↑(V ω) * Complex.I)‖ ≤ 1 := fun ω => by
    rw [show (↑ξ * ↑(V ω) * Complex.I : ℂ) = ↑(ξ * V ω) * Complex.I from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hbW : ∀ ω, ‖Complex.exp (↑ξ * ↑(W ω) * Complex.I)‖ ≤ 1 := fun ω => by
    rw [show (↑ξ * ↑(W ω) * Complex.I : ℂ) = ↑(ξ * W ω) * Complex.I from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hIV : Integrable (fun ω => Complex.exp (↑ξ * ↑(V ω) * Complex.I)) μ :=
    Integrable.of_bound hgV.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbV)
  have hIW : Integrable (fun ω => Complex.exp (↑ξ * ↑(W ω) * Complex.I)) μ :=
    Integrable.of_bound hgW.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbW)
  rw [charFun_apply_real, charFun_apply_real,
    integral_map hV (by fun_prop), integral_map hW (by fun_prop),
    ← integral_sub hIV hIW]
  calc ‖∫ ω, (Complex.exp (↑ξ * ↑(V ω) * Complex.I)
            - Complex.exp (↑ξ * ↑(W ω) * Complex.I)) ∂μ‖
      ≤ ∫ ω, ‖Complex.exp (↑ξ * ↑(V ω) * Complex.I)
            - Complex.exp (↑ξ * ↑(W ω) * Complex.I)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, |ξ| * |V ω - W ω| ∂μ := by
        refine integral_mono ((hIV.sub hIW).norm) (hVW.abs.const_mul |ξ|) fun ω => ?_
        have hfactor : Complex.exp (↑ξ * ↑(V ω) * Complex.I)
              - Complex.exp (↑ξ * ↑(W ω) * Complex.I)
            = Complex.exp (↑ξ * ↑(W ω) * Complex.I)
              * (Complex.exp (Complex.I * ↑(ξ * (V ω - W ω))) - 1) := by
          rw [mul_sub, mul_one, ← Complex.exp_add]
          congr 2
          push_cast; ring
        rw [hfactor, norm_mul,
          show (↑ξ * ↑(W ω) * Complex.I : ℂ) = ↑(ξ * W ω) * Complex.I from by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, one_mul]
        calc ‖Complex.exp (Complex.I * ↑(ξ * (V ω - W ω))) - 1‖
            ≤ ‖ξ * (V ω - W ω)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
          _ = |ξ| * |V ω - W ω| := by rw [Real.norm_eq_abs, abs_mul]
    _ = |ξ| * ∫ ω, |V ω - W ω| ∂μ := integral_const_mul _ _
