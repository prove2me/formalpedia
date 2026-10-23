-- Prove2me | solution 1 for RiskFunctionals.Deviation.std_representation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:28:10.523358+00:00
-- url     : https://prove2.me/submissions/5950a3e0-eb6f-48d7-9b6e-7d6535a2f222

import Mathlib

open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (hY2 : MemLp Y 2 P) :
    Real.sqrt (variance Y P) = (eLpNorm (fun ω => Y ω - ∫ ω', Y ω' ∂P) 2 P).toReal ∧
    ((Real.sqrt (variance Y P) : ℝ) : EReal) =
      ⨆ Z ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z 2 P ∧ ∫ ω, Z ω ∂P = 0 ∧
          ∫ ω, Z ω ^ 2 ∂P ≤ 1},
        ((∫ ω, Y ω * Z ω ∂P : ℝ) : EReal) := by
  set m := ∫ ω, Y ω ∂P with hm
  set W : Ω → ℝ := fun ω => Y ω - m with hW
  have hWL : MemLp W 2 P := hY2.sub (memLp_const m)
  have hvar : variance Y P = ∫ ω, W ω ^ 2 ∂P := variance_eq_integral hY.aemeasurable
  set σ := Real.sqrt (variance Y P) with hσ
  have hv0 : 0 ≤ variance Y P := variance_nonneg _ _
  have hσ2 : σ ^ 2 = ∫ ω, W ω ^ 2 ∂P := by rw [hσ, Real.sq_sqrt hv0, hvar]
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hW2i : Integrable (fun ω => W ω ^ 2) P := hWL.integrable_sq
  have he1 : ∀ Z : Ω → ℝ, MemLp Z 2 P → ∫ ω, Z ω ∂P = 0 →
      ∫ ω, Y ω * Z ω ∂P = ∫ ω, W ω * Z ω ∂P := by
    intro Z hZL hZ0
    have hYZ : Integrable (fun ω => Y ω * Z ω) P := hY2.integrable_mul hZL
    have : (fun ω => W ω * Z ω) = fun ω => Y ω * Z ω - m * Z ω := by
      funext ω; simp only [hW]; ring
    rw [this, integral_sub hYZ ((hZL.integrable one_le_two).const_mul m), integral_const_mul,
      hZ0]; ring
  constructor
  · rw [hWL.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    have : (∫ a, ‖W a‖ ^ (2 : ENNReal).toReal ∂P) = ∫ a, W a ^ 2 ∂P := by
      congr 1; ext a
      rw [show (2 : ENNReal).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        Real.norm_eq_abs, sq_abs]
    rw [this, ENNReal.toReal_ofReal (by positivity), ← hvar, hσ, Real.sqrt_eq_rpow]
    norm_num
  · apply le_antisymm
    · -- attainment
      by_cases hs : σ = 0
      · rw [hs]
        refine le_trans ?_ (le_iSup₂ (f := fun Z (_ : Z ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z 2 P ∧
            ∫ ω, Z ω ∂P = 0 ∧ ∫ ω, Z ω ^ 2 ∂P ≤ 1}) => ((∫ ω, Y ω * Z ω ∂P : ℝ) : EReal))
          (fun _ => (0:ℝ)) ⟨measurable_const, memLp_const 0, by simp, by simp⟩)
        simp
      · have hσp : 0 < σ := lt_of_le_of_ne hσ0 (Ne.symm hs)
        set Z : Ω → ℝ := fun ω => σ⁻¹ * W ω with hZ
        have hZm : Measurable Z := (hY.sub measurable_const).const_mul σ⁻¹
        have hZL : MemLp Z 2 P := hWL.const_mul σ⁻¹
        have hWi : ∫ ω, W ω ∂P = 0 := by
          rw [integral_sub (hY2.integrable one_le_two) (integrable_const m), integral_const]; simp [hm]
        have hZ0 : ∫ ω, Z ω ∂P = 0 := by rw [integral_const_mul, hWi, mul_zero]
        have hZ2 : ∫ ω, Z ω ^ 2 ∂P = 1 := by
          have : (fun ω => Z ω ^ 2) = fun ω => σ⁻¹ ^ 2 * W ω ^ 2 := by funext ω; simp only [hZ]; ring
          rw [this, integral_const_mul, ← hσ2]; field_simp
        have hval : ∫ ω, Y ω * Z ω ∂P = σ := by
          rw [he1 Z hZL hZ0]
          have : (fun ω => W ω * Z ω) = fun ω => σ⁻¹ * W ω ^ 2 := by funext ω; simp only [hZ]; ring
          rw [this, integral_const_mul, ← hσ2]; field_simp
        refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun Z (_ : Z ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z 2 P ∧
            ∫ ω, Z ω ∂P = 0 ∧ ∫ ω, Z ω ^ 2 ∂P ≤ 1}) => ((∫ ω, Y ω * Z ω ∂P : ℝ) : EReal))
          Z ⟨hZm, hZL, hZ0, hZ2.le⟩)
        rw [hval]
    · refine iSup₂_le fun Z hZ => ?_
      obtain ⟨hZm, hZL, hZ0, hZ2⟩ := hZ
      rw [EReal.coe_le_coe_iff]
      have hWZ : Integrable (fun ω => W ω * Z ω) P := hWL.integrable_mul hZL
      have hZ2i : Integrable (fun ω => Z ω ^ 2) P := hZL.integrable_sq
      rw [he1 Z hZL hZ0]
      by_cases hs : σ = 0
      · have hW0 : ∫ ω, W ω ^ 2 ∂P = 0 := by rw [← hσ2, hs]; ring
        have hae : W =ᵐ[P] 0 := by
          have := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (W ω)) hW2i).1 hW0
          filter_upwards [this] with ω hω
          simpa using hω
        have : ∫ ω, W ω * Z ω ∂P = 0 := by
          rw [integral_eq_zero_of_ae]
          filter_upwards [hae] with ω hω; simp [hω]
        rw [this, hs]
      · have hσp : 0 < σ := lt_of_le_of_ne hσ0 (Ne.symm hs)
        have hpt : ∀ ω, W ω * Z ω ≤ (1 / (2 * σ)) * W ω ^ 2 + (σ / 2) * Z ω ^ 2 := by
          intro ω
          have : 0 ≤ (W ω - σ * Z ω) ^ 2 / (2 * σ) := by positivity
          have e : (1 / (2 * σ)) * W ω ^ 2 + (σ / 2) * Z ω ^ 2 - W ω * Z ω =
              (W ω - σ * Z ω) ^ 2 / (2 * σ) := by
            field_simp; ring
          linarith
        have hI : Integrable (fun ω => (1 / (2 * σ)) * W ω ^ 2 + (σ / 2) * Z ω ^ 2) P :=
          (hW2i.const_mul _).add (hZ2i.const_mul _)
        have := integral_mono hWZ hI hpt
        have e : ∫ ω, ((1 / (2 * σ)) * W ω ^ 2 + (σ / 2) * Z ω ^ 2) ∂P =
            (1 / (2 * σ)) * σ ^ 2 + (σ / 2) * ∫ ω, Z ω ^ 2 ∂P := by
          rw [integral_add (hW2i.const_mul _) (hZ2i.const_mul _), integral_const_mul,
            integral_const_mul, ← hσ2]
        rw [e] at this
        have h2 : σ / 2 * ∫ ω, Z ω ^ 2 ∂P ≤ σ / 2 := by
          have := mul_le_mul_of_nonneg_left hZ2 (by positivity : (0:ℝ) ≤ σ / 2); linarith
        have h3 : 1 / (2 * σ) * σ ^ 2 = σ / 2 := by field_simp
        linarith
