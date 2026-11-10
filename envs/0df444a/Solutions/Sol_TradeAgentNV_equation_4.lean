-- Prove2me | solution 1 for TradeAgentNV.equation_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T04:20:38.718834+00:00
-- url     : https://prove2.me/submissions/f6313ca8-293e-43c4-b1c7-6140477610c9

import Mathlib
import Definitions.Def_TradeAgentNV_winProb
import Definitions.Def_TradeAgentNV_expProfit
import Definitions.Def_TradeAgentNV_expBenefit

open MeasureTheory ProbabilityTheory

open TradeAgentNV in
theorem solution
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z U : Ω → ℝ) (hZ : Measurable Z) (hU : Measurable U) (hZU : IndepFun Z U P)
    (hZ0 : P.real {ω | Z ω ≤ 0} = 0)
    (w' : ℝ → ℝ)
    (hw : ∀ b, 0 ≤ b → HasDerivWithinAt (winProb P Z) (w' b) (Set.Ici 0) b)
    (hw'pos : ∀ b, 0 ≤ b → 0 < w' b)
    (hU01 : ∀ᵐ ω ∂P, U ω ∈ Set.Icc (0 : ℝ) 1) (hEU : 0 < ∫ ω, U ω ∂P)
    (r t h π D q : ℝ) (hr : 0 < r) (ht : 0 < t) (hh : 0 < h) (hπ : 0 < π) (hD : 0 < D)
    (hq : 0 < q) (hrtπ : 0 < r - t + π) :
    ∀ b, 0 ≤ b → expProfit P Z U r t h π D q b =
      winProb P Z b * (expBenefit P U r t h π D q - b * q) - π * D := by
  intro b hb
  have hρ : 0 < rho r t h π := by unfold rho; linarith
  have wp : ∀ u, wonProfit r t h π D q b u
      = rho r t h π * min (q * u) D - h * q * u - b * q - π * D := by
    intro u
    unfold wonProfit rho
    rcases le_total (q * u) D with hle | hle
    · rw [min_eq_left hle, max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [min_eq_right hle, max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℝ, φ = fun z => if z ≤ b then (1 : ℝ) else 0 := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun u => rho r t h π * min (q * u) D - h * q * u - b * q :=
    ⟨_, rfl⟩
  have hφm : Measurable φ := by
    rw [hφ]
    exact Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
      measurable_const
  have hgc : Continuous g := by
    rw [hg]
    exact ((continuous_const.mul ((continuous_const.mul continuous_id).min continuous_const)).sub
      (continuous_const.mul continuous_id)).sub continuous_const
  have hgm : Measurable g := hgc.measurable
  set C := rho r t h π * D + h * q + b * q with hC
  have hC0 : 0 ≤ C := by positivity
  have hgb : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖g u‖ ≤ C := by
    rintro u ⟨h0, h1⟩
    have m0 : 0 ≤ min (q * u) D := le_min (by positivity) hD.le
    have m1 : min (q * u) D ≤ D := min_le_right _ _
    have hm : rho r t h π * min (q * u) D ≤ rho r t h π * D := mul_le_mul_of_nonneg_left m1 hρ.le
    have hm0 : 0 ≤ rho r t h π * min (q * u) D := mul_nonneg hρ.le m0
    have hu : h * q * u ≤ h * q := by nlinarith [mul_pos hh hq]
    have hu0 : 0 ≤ h * q * u := by positivity
    have hbq : 0 ≤ b * q := by positivity
    rw [hg, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hUi : Integrable U P := Integrable.of_bound hU.aestronglyMeasurable 1
    (hU01.mono fun ω hω => by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hω.1, hω.2])
  have hMm : Measurable (fun ω => min (q * U ω) D) := (measurable_const.mul hU).min measurable_const
  have hMi : Integrable (fun ω => min (q * U ω) D) P := Integrable.of_bound hMm.aestronglyMeasurable D
    (hU01.mono fun ω hω => by
      have m0 : 0 ≤ min (q * U ω) D := le_min (mul_nonneg hq.le hω.1) hD.le
      rw [Real.norm_eq_abs, abs_of_nonneg m0]
      exact min_le_right _ _)
  have hprodm : Measurable ((φ ∘ Z) * (g ∘ U)) := (hφm.comp hZ).mul (hgm.comp hU)
  have hprodi : Integrable ((φ ∘ Z) * (g ∘ U)) P := Integrable.of_bound hprodm.aestronglyMeasurable C
    (hU01.mono fun ω hω => by
      show ‖φ (Z ω) * g (U ω)‖ ≤ C
      rw [norm_mul]
      have hφ1 : ‖φ (Z ω)‖ ≤ 1 := by
        rw [hφ]
        by_cases hz : Z ω ≤ b <;> simp [hz]
      calc ‖φ (Z ω)‖ * ‖g (U ω)‖ ≤ 1 * C := mul_le_mul hφ1 (hgb _ hω) (norm_nonneg _) zero_le_one
        _ = C := one_mul C)
  have hpt : (fun ω => if Z ω ≤ b then wonProfit r t h π D q b (U ω) else -(π * D))
      = fun ω => ((φ ∘ Z) * (g ∘ U)) ω - π * D := by
    funext ω
    show _ = φ (Z ω) * g (U ω) - π * D
    rw [hφ, hg]
    dsimp only
    by_cases hz : Z ω ≤ b
    · rw [if_pos hz, if_pos hz, wp]; ring
    · rw [if_neg hz, if_neg hz]; ring
  have hφZ : ∫ ω, (φ ∘ Z) ω ∂P = winProb P Z b := by
    have e : (φ ∘ Z) = Set.indicator {ω | Z ω ≤ b} 1 := by
      funext ω
      rw [hφ]
      by_cases hz : Z ω ≤ b
      · simp [hz, Set.indicator_of_mem (show ω ∈ {ω | Z ω ≤ b} from hz)]
      · simp [hz, Set.indicator_of_notMem (show ω ∉ {ω | Z ω ≤ b} from hz)]
    rw [e, integral_indicator_one (measurableSet_le hZ measurable_const)]
    rfl
  have hgU : ∫ ω, (g ∘ U) ω ∂P
      = rho r t h π * ∫ ω, min (q * U ω) D ∂P - h * q * ∫ ω, U ω ∂P - b * q := by
    have e : (g ∘ U) = fun ω => rho r t h π * min (q * U ω) D - h * q * U ω - b * q := by
      funext ω; rw [hg]; rfl
    have i1 : Integrable (fun ω => rho r t h π * min (q * U ω) D) P := hMi.const_mul _
    have i2 : Integrable (fun ω => h * q * U ω) P := hUi.const_mul _
    have i12 : Integrable (fun ω => rho r t h π * min (q * U ω) D - h * q * U ω) P := i1.sub i2
    rw [e]
    show ∫ ω, (rho r t h π * min (q * U ω) D - h * q * U ω - b * q) ∂P = _
    rw [integral_sub i12 (integrable_const _), integral_sub i1 i2, integral_const_mul,
      integral_const_mul, integral_const, probReal_univ, one_smul]
  unfold expProfit expBenefit
  rw [hpt, integral_sub hprodi (integrable_const _), integral_const, probReal_univ, one_smul,
    (hZU.comp hφm hgm).integral_mul_eq_mul_integral (hφm.comp hZ).aestronglyMeasurable
      (hgm.comp hU).aestronglyMeasurable, hφZ, hgU]
