-- Prove2me | solution 1 for SeatInventory.Gaussian.protection_level_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T13:59:14.642107+00:00
-- url     : https://prove2.me/submissions/e62ee243-35d5-477b-b8d1-fe086256ff74

import Mathlib
import Definitions.Def_SeatInventory_Gaussian_Model

open MeasureTheory ProbabilityTheory

set_option autoImplicit false

namespace A7ed1035

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian Set Filter Topology

lemma cont_pdf (m : ℝ) (v : NNReal) : Continuous (gaussianPDFReal m v) := by
  rw [gaussianPDFReal_def]
  fun_prop

lemma real_Iic (m : ℝ) {v : NNReal} (hv : v ≠ 0) (S : ℝ) :
    (gaussianReal m v).real (Iic S) = ∫ x in Iic S, gaussianPDFReal m v x := by
  rw [measureReal_def, gaussianReal_apply_eq_integral _ hv, ENNReal.toReal_ofReal]
  exact setIntegral_nonneg measurableSet_Iic (fun x _ => gaussianPDFReal_nonneg _ _ _)

lemma cdf_formula (m : ℝ) {v : NNReal} (hv : v ≠ 0) (S : ℝ) :
    cdf (gaussianReal m v) S
      = cdf (gaussianReal m v) 0 + ∫ x in (0:ℝ)..S, gaussianPDFReal m v x := by
  rw [cdf_eq_real, cdf_eq_real, real_Iic m hv, real_Iic m hv,
    ← intervalIntegral.integral_Iic_sub_Iic (integrable_gaussianPDFReal m v).integrableOn
      (integrable_gaussianPDFReal m v).integrableOn]
  ring

lemma tail_eq (m : ℝ) {v : NNReal} (hv : v ≠ 0) (S : ℝ) :
    tailProb (gaussianReal m v) S = 1 - cdf (gaussianReal m v) S := by
  have := nullSingletonClass_gaussianReal (μ := m) hv
  have h1 : (gaussianReal m v).real (Ici S) + (gaussianReal m v).real (Iio S) = 1 := by
    rw [← measureReal_union (by
        rw [Set.disjoint_left]; intro x hx hx'; exact (not_lt.mpr (mem_Ici.mp hx)) hx')
      measurableSet_Iio, Set.Ici_union_Iio, probReal_univ]
  have h2 : (gaussianReal m v).real (Iio S) = (gaussianReal m v).real (Iic S) := by
    rw [measureReal_def, measureReal_def, measure_congr Iio_ae_eq_Iic]
  unfold tailProb
  rw [cdf_eq_real, ← measureReal_def]
  linarith

theorem main (rbar σ f₁ f₂ : ℝ) (hσ : 0 < σ) (hf₂ : 0 < f₂) (hf : f₂ < f₁) :
    ∃! S : ℝ, IsProtectionLevel rbar σ f₁ f₂ S := by
  set v : NNReal := ⟨σ ^ 2, sq_nonneg σ⟩ with hvdef
  have hv : v ≠ 0 := by
    intro h
    have h' : σ ^ 2 = 0 := congrArg (fun x : NNReal => (x : ℝ)) h
    have : 0 < σ ^ 2 := by positivity
    linarith
  set μ := gaussianReal rbar v
  set F := cdf μ
  have hF : ∀ S, F S = F 0 + ∫ x in (0:ℝ)..S, gaussianPDFReal rbar v x :=
    cdf_formula rbar hv
  have hderiv : ∀ S, HasDerivAt F (gaussianPDFReal rbar v S) S := by
    intro S
    have := ((cont_pdf rbar v).integral_hasStrictDerivAt 0 S).hasDerivAt.const_add (F 0)
    have hfun : F = fun u => F 0 + ∫ x in (0:ℝ)..u, gaussianPDFReal rbar v x := funext hF
    rw [hfun]
    exact this
  have hcont : Continuous F := continuous_iff_continuousAt.mpr
    (fun S => (hderiv S).continuousAt)
  have hmono : StrictMono F := strictMono_of_hasDerivAt_pos hderiv
    (fun S => gaussianPDFReal_pos _ _ _ hv)
  have htail : ∀ S, IsProtectionLevel rbar σ f₁ f₂ S ↔ F S = 1 - f₂ / f₁ := by
    intro S
    unfold IsProtectionLevel gaussianLaw
    rw [show gaussianReal rbar ⟨σ ^ 2, sq_nonneg σ⟩ = μ from rfl, tail_eq rbar hv]
    constructor <;> intro h <;> linarith
  have hf₁ : 0 < f₁ := hf₂.trans hf
  have hp0 : 0 < f₂ / f₁ := div_pos hf₂ hf₁
  have hp1 : f₂ / f₁ < 1 := (div_lt_one hf₁).mpr hf
  have hbot : Tendsto F atBot (𝓝 0) := tendsto_cdf_atBot μ
  have htop : Tendsto F atTop (𝓝 1) := tendsto_cdf_atTop μ
  have h1 : ∃ a, F a ≤ 1 - f₂ / f₁ := by
    have := (hbot.eventually (gt_mem_nhds (show (0:ℝ) < 1 - f₂ / f₁ by linarith))).exists
    obtain ⟨a, ha⟩ := this
    exact ⟨a, ha.le⟩
  have h2 : ∃ b, 1 - f₂ / f₁ ≤ F b := by
    have := (htop.eventually (lt_mem_nhds (show 1 - f₂ / f₁ < (1:ℝ) by linarith))).exists
    obtain ⟨b, hb⟩ := this
    exact ⟨b, hb.le⟩
  obtain ⟨S, hS⟩ := mem_range_of_exists_le_of_exists_ge hcont h1 h2
  refine ⟨S, (htail S).mpr hS, fun T hT => ?_⟩
  exact hmono.injective (((htail T).mp hT).trans hS.symm)

end A7ed1035

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem solution (rbar σ f₁ f₂ : ℝ) (hσ : 0 < σ) (hf₂ : 0 < f₂)
    (hf : f₂ < f₁) :
    ∃! S : ℝ, IsProtectionLevel rbar σ f₁ f₂ S := by
  exact A7ed1035.main rbar σ f₁ f₂ hσ hf₂ hf
